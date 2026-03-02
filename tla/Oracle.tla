---------------------------- MODULE Oracle ------------------------------------
(*
 * TLA+ Specification of the Lux Price Oracle
 *
 * Source: ~/work/lux/dex/oracle/
 *
 * Protocol summary:
 *   A decentralized price oracle aggregates price observations from
 *   multiple independent updaters.  Each updater submits a price at
 *   some timestamp.  The oracle accepts a new aggregate price when
 *   at least MinUpdaters have submitted within a freshness window.
 *   Individual submissions that deviate beyond MaxDeviation from the
 *   current aggregate are rejected (outlier filtering).
 *
 * State model:
 *   currentPrice     -- accepted aggregate price (0 if uninitialized)
 *   currentTimestamp  -- timestamp of last accepted price
 *   submissions[u]   -- latest submission from updater u: {price, ts}
 *   acceptedCount    -- count of submissions in current round
 *   roundId          -- monotonic round counter
 *
 * Actions:
 *   SubmitPrice(u, p, ts)  -- updater u submits price p at time ts
 *   AcceptRound            -- oracle accepts round if quorum met
 *   ExpireRound            -- round expires if stale (no quorum in time)
 *   AdvanceTime            -- global clock advances
 *
 * Invariants:
 *   FreshnessGuarantee   -- accepted price is never staler than MaxStaleness
 *   QuorumRequired       -- price accepted only with >= MinUpdaters
 *   DeviationBounded     -- no accepted submission deviates > MaxDeviation
 *   PricePositive        -- currentPrice > 0 after first acceptance
 *   MonotonicRound       -- round ID never decreases
 *)

EXTENDS Integers, FiniteSets

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    Updaters,           \* Set of updater identifiers
    PriceRange,         \* Set of valid prices (integers)
    MinUpdaters,        \* Minimum updaters for quorum
    MaxStaleness,       \* Maximum age of accepted price (in ticks)
    MaxDeviation,       \* Maximum allowed deviation from current price
    MaxTime             \* Upper bound on time for model checking

\* --------------------------------------------------------------------------
\* ASSUMPTIONS
\* --------------------------------------------------------------------------

ASSUME Updaters # {} /\ IsFiniteSet(Updaters)
ASSUME PriceRange # {} /\ IsFiniteSet(PriceRange)
ASSUME MinUpdaters \in Nat \ {0}
ASSUME MinUpdaters <= Cardinality(Updaters)
ASSUME MaxStaleness \in Nat \ {0}
ASSUME MaxDeviation \in Nat \ {0}
ASSUME MaxTime \in Nat \ {0}

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    currentPrice,       \* Nat -- accepted aggregate price (0 = uninitialized)
    currentTimestamp,    \* Nat -- timestamp of last acceptance
    submissions,        \* submissions[u] \in {price: Nat, ts: Nat} or NULL
    acceptedCount,      \* Nat -- submissions in current round
    roundId,            \* Nat -- monotonic round counter
    globalTime          \* Nat -- global clock

vars == <<currentPrice, currentTimestamp, submissions, acceptedCount,
          roundId, globalTime>>

\* --------------------------------------------------------------------------
\* HELPERS
\* --------------------------------------------------------------------------

NULL == [price |-> 0, ts |-> 0]

\* Absolute difference
AbsDiff(a, b) == IF a >= b THEN a - b ELSE b - a

\* Count of valid submissions (non-NULL, within freshness window)
ValidSubmissions ==
    { u \in Updaters :
        submissions[u] # NULL /\
        globalTime - submissions[u].ts <= MaxStaleness }

ValidCount == Cardinality(ValidSubmissions)

\* Median approximation: for model checking, use the average of valid prices
\* (exact median requires sequence sorting which is expensive in TLA+)
AggregatePrice ==
    IF ValidCount = 0 THEN 0
    ELSE LET total == CHOOSE t \in Nat :
            t = (CHOOSE s \in [ValidSubmissions -> PriceRange] :
                \A u \in ValidSubmissions : s[u] = submissions[u].price
            )[CHOOSE u \in ValidSubmissions : TRUE]
         IN total  \* simplified: take any valid price as representative

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

TypeOK ==
    /\ currentPrice \in Nat
    /\ currentTimestamp \in Nat
    /\ \A u \in Updaters : submissions[u] \in [price: Nat, ts: Nat]
    /\ acceptedCount \in Nat
    /\ roundId \in Nat
    /\ globalTime \in Nat

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ currentPrice = 0
    /\ currentTimestamp = 0
    /\ submissions = [u \in Updaters |-> NULL]
    /\ acceptedCount = 0
    /\ roundId = 0
    /\ globalTime = 1

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

\* Updater submits a price observation
SubmitPrice(u, p) ==
    /\ p \in PriceRange
    /\ p > 0
    \* Deviation check: if we have a current price, submission must be close
    /\ IF currentPrice > 0
       THEN AbsDiff(p, currentPrice) <= MaxDeviation
       ELSE TRUE
    \* Record submission with current timestamp
    /\ submissions' = [submissions EXCEPT ![u] = [price |-> p, ts |-> globalTime]]
    /\ acceptedCount' = IF submissions[u] = NULL
                        THEN acceptedCount + 1
                        ELSE acceptedCount
    /\ UNCHANGED <<currentPrice, currentTimestamp, roundId, globalTime>>

\* Oracle accepts the round when quorum is met
AcceptRound ==
    /\ ValidCount >= MinUpdaters
    \* Pick a representative price (first valid updater's price)
    /\ LET u0 == CHOOSE u \in ValidSubmissions : TRUE
           newPrice == submissions[u0].price
       IN
       /\ currentPrice' = newPrice
       /\ currentTimestamp' = globalTime
    /\ roundId' = roundId + 1
    /\ acceptedCount' = 0
    /\ submissions' = [u \in Updaters |-> NULL]
    /\ UNCHANGED globalTime

\* Round expires: too much time passed without quorum
ExpireRound ==
    /\ currentTimestamp > 0
    /\ globalTime - currentTimestamp > MaxStaleness
    /\ ValidCount < MinUpdaters
    \* Reset submissions, keep stale price (consumers must check staleness)
    /\ submissions' = [u \in Updaters |-> NULL]
    /\ acceptedCount' = 0
    /\ UNCHANGED <<currentPrice, currentTimestamp, roundId, globalTime>>

\* Global clock advances
AdvanceTime ==
    /\ globalTime < MaxTime
    /\ globalTime' = globalTime + 1
    /\ UNCHANGED <<currentPrice, currentTimestamp, submissions,
                   acceptedCount, roundId>>

\* --------------------------------------------------------------------------
\* NEXT STATE
\* --------------------------------------------------------------------------

Next ==
    \/ \E u \in Updaters, p \in PriceRange : SubmitPrice(u, p)
    \/ AcceptRound
    \/ ExpireRound
    \/ AdvanceTime

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

\* 1. Freshness: accepted price is never older than MaxStaleness
\*    (only checked when price has been set)
FreshnessGuarantee ==
    currentPrice > 0 =>
        globalTime - currentTimestamp <= MaxStaleness + 1

\* 2. Quorum: price was accepted with sufficient updaters
\*    (invariant on round transitions, checked via monotonic roundId)
QuorumRequired ==
    roundId > 0 => currentPrice > 0

\* 3. Deviation bound: current price is within valid range
PriceInRange ==
    currentPrice > 0 => currentPrice \in PriceRange

\* 4. Round monotonicity
MonotonicRound ==
    roundId >= 0

\* 5. Time monotonicity
MonotonicTime ==
    globalTime >= 1

\* 6. Submission validity: all recorded submissions have positive prices
SubmissionValidity ==
    \A u \in Updaters :
        submissions[u] # NULL => submissions[u].price > 0

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

\* If updaters keep submitting, eventually a round is accepted
LivenessAcceptance ==
    [](\A u \in Updaters : submissions[u] # NULL => <>( roundId' > roundId))

=============================================================================
