---------------------------- MODULE Wave -----------------------------------
(*
 * TLA+ Specification of the Lux Wave Consensus Protocol
 * (Snow-family with Fast Probabilistic Consensus)
 *
 * Source: ~/work/lux/consensus/protocol/wave/wave.go
 * Safety proof: ~/work/lux/formal/lean/Consensus/Safety.lean
 *
 * Protocol summary:
 *   In each round, ALL validators sample k peers and collect binary votes.
 *   Each validator then checks whether yes-votes or no-votes meet an alpha
 *   threshold:
 *   - Threshold met in same direction as preference: confidence++
 *   - Threshold met in opposite direction: preference flips, confidence = 1
 *   - Neither side meets threshold: confidence = 0
 *   When confidence reaches beta consecutive rounds, the validator finalizes
 *   (Accept or Reject). Once finalized, it skips future rounds for that item.
 *
 * Key safety insight (Safety.lean unique_threshold, line 107):
 *   With alpha > 2k/3 and f < n/3 Byzantine nodes, in any single round
 *   at most ONE direction can meet the alpha threshold across ALL samples.
 *   This is because honest nodes vote their single preference, and even
 *   with all f Byzantine nodes voting adversarially, the honest majority
 *   prevents two conflicting values from both reaching alpha.
 *
 * Model structure:
 *   Each round has two phases:
 *   1. Environment picks a "roundDir" for value v: the direction ("yes",
 *      "no", or "none") that CAN meet alpha this round. This models the
 *      unique_threshold constraint globally across all validators.
 *   2. Each honest validator sees a vote count consistent with roundDir.
 *      Within the winning direction, a validator may or may not individually
 *      see enough votes (sample variation), but no validator sees the
 *      OPPOSITE direction reaching alpha.
 *
 * Go-to-TLA+ mapping:
 *   wave.Config.K           -> K
 *   ceil(Config.Alpha * K)  -> AlphaThreshold
 *   wave.Config.Beta        -> Beta
 *   wave.prefs[item]        -> pref[v][i]       (BOOLEAN)
 *   WaveState.Count         -> conf[v][i]        (0..Beta)
 *   WaveState.Decided       -> decided[v][i]     (BOOLEAN)
 *   WaveState.Result        -> decision[v][i]    ({"Accept","Reject","Undecided"})
 *   fpc.Selector            -> AlphaThreshold    (constant; sound for safety)
 *   prism.Cut.Sample        -> nondeterministic per-validator vote count
 *   Transport.RequestVotes  -> nondeterministic per-validator vote count
 *)

EXTENDS Integers, FiniteSets

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    N,              \* Total validators              (Lean: Params.n)
    F,              \* Max Byzantine validators       (Lean: Params.f, f < n/3)
    K,              \* Sample size per round          (wave.Config.K)
    AlphaThreshold, \* Vote threshold                 (ceil(alpha * k))
    Beta,           \* Consecutive rounds to finalize (wave.Config.Beta)
    Values          \* Set of values to decide        (e.g. {"v1"})

\* --------------------------------------------------------------------------
\* ASSUMPTIONS (mirror Lean Params constraints in Safety.lean:44-53)
\* --------------------------------------------------------------------------

ASSUME N \in Nat \ {0}
ASSUME F \in Nat /\ 3 * F < N                  \* BFT bound: f < n/3
ASSUME K \in 1..N                               \* k <= n
ASSUME AlphaThreshold \in 1..K                  \* alpha <= k
ASSUME Beta \in Nat \ {0}                       \* beta > 0
ASSUME Values # {} /\ IsFiniteSet(Values)
ASSUME 3 * AlphaThreshold > 2 * K              \* alpha > 2k/3 (Safety.lean:107)

\* --------------------------------------------------------------------------
\* Decision values (maps to types.Decision in core/types/types.go)
\* --------------------------------------------------------------------------

Accept    == "Accept"      \* types.DecideAccept
Reject    == "Reject"      \* types.DecideReject
Undecided == "Undecided"   \* types.DecideUndecided

Decisions == {Accept, Reject, Undecided}

\* Directions that can "win" a round (meet alpha threshold)
Directions == {"yes", "no", "none"}

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    pref,       \* pref[v][i] \in BOOLEAN         -- wave.prefs[item]
    conf,       \* conf[v][i] \in 0..Beta          -- WaveState.Count
    decided,    \* decided[v][i] \in BOOLEAN       -- WaveState.Decided
    decision,   \* decision[v][i] \in Decisions    -- WaveState.Result
    round,      \* round \in Nat                   -- global round counter
    byz         \* byz \subseteq Validators        -- fixed Byzantine set

vars == <<pref, conf, decided, decision, round, byz>>

\* --------------------------------------------------------------------------
\* DERIVED SETS
\* --------------------------------------------------------------------------

Validators == 1..N

Honest == Validators \ byz

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

TypeOK ==
    /\ pref     \in [Values -> [Validators -> BOOLEAN]]
    /\ conf     \in [Values -> [Validators -> 0..Beta]]
    /\ decided  \in [Values -> [Validators -> BOOLEAN]]
    /\ decision \in [Values -> [Validators -> Decisions]]
    /\ round    \in Nat
    /\ byz      \subseteq Validators
    /\ Cardinality(byz) <= F

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

(*
 * Maps to wave.New() in wave.go:62-86:
 *   states = make(map[T]*WaveState)  -> undecided, count=0
 *   prefs  = make(map[T]bool)        -> false (Go zero value)
 *)
Init ==
    /\ \E b \in SUBSET Validators :
        /\ Cardinality(b) <= F
        /\ byz = b
    /\ pref     = [v \in Values |-> [i \in Validators |-> FALSE]]
    /\ conf     = [v \in Values |-> [i \in Validators |-> 0]]
    /\ decided  = [v \in Values |-> [i \in Validators |-> FALSE]]
    /\ decision = [v \in Values |-> [i \in Validators |-> Undecided]]
    /\ round    = 0

\* --------------------------------------------------------------------------
\* HELPER: Apply vote outcome to a single validator's state
\* --------------------------------------------------------------------------

(*
 * ApplyVote(v, i, yesVotes):
 *   Computes the next state for validator i on value v given yesVotes
 *   out of K total. Directly encodes wave.go lines 133-187.
 *
 *   Returns a record with the new values of pref, conf, decided, decision
 *   for this validator. (In TLA+, we use this as a predicate that constrains
 *   the primed variables.)
 *)

\* Compute new confidence given current pref matches vote direction
NewConf(curConf, prefMatches) ==
    IF prefMatches THEN curConf + 1 ELSE 1

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

(*
 * RoundStep(v):
 *   One complete round of Wave consensus for value v.
 *   ALL honest validators participate simultaneously.
 *
 *   The environment first chooses a roundDir -- the direction that CAN
 *   meet alpha threshold this round. This models unique_threshold:
 *   with alpha > 2k/3 and honest majority, at most one direction can
 *   reach threshold in any round across all samplings.
 *
 *   Then each honest validator nondeterministically sees a vote count
 *   consistent with roundDir:
 *   - roundDir = "yes": each validator's yesVotes >= alpha OR
 *                        yesVotes < alpha (sample didn't have enough),
 *                        but noVotes is ALWAYS < alpha.
 *   - roundDir = "no":  symmetrically, noVotes might reach alpha but
 *                        yesVotes is ALWAYS < alpha.
 *   - roundDir = "none": neither direction reaches alpha for anyone.
 *
 *   This models wave.go Wave.Tick being called on all validators in
 *   the same consensus round. In the Go code, the engine loop calls
 *   Tick for each pending item on each validator.
 *)
RoundStep(v) ==
    \E roundDir \in Directions :
        \* For each honest, undecided validator, pick a consistent vote count.
        \* Decided validators are skipped (wave.go:99-102).
        \E voteFn \in [Honest -> 0..K] :
            \* Constraint: all vote counts must be consistent with roundDir
            /\ \A i \in Honest :
                ~decided[v][i] =>
                    CASE roundDir = "yes" ->
                        \* noVotes cannot reach alpha
                        (K - voteFn[i]) < AlphaThreshold
                      [] roundDir = "no" ->
                        \* yesVotes cannot reach alpha
                        voteFn[i] < AlphaThreshold
                      [] roundDir = "none" ->
                        \* neither reaches alpha
                        /\ voteFn[i] < AlphaThreshold
                        /\ (K - voteFn[i]) < AlphaThreshold
            \* Apply the vote outcome to each honest validator
            /\ pref' = [pref EXCEPT
                ![v] = [i \in Validators |->
                    IF i \notin Honest \/ decided[v][i] THEN pref[v][i]
                    ELSE LET yv == voteFn[i]
                             nv == K - yv
                         IN IF yv >= AlphaThreshold THEN TRUE
                            ELSE IF nv >= AlphaThreshold THEN FALSE
                            ELSE pref[v][i]]]
            /\ conf' = [conf EXCEPT
                ![v] = [i \in Validators |->
                    IF i \notin Honest \/ decided[v][i] THEN conf[v][i]
                    ELSE LET yv == voteFn[i]
                             nv == K - yv
                         IN IF yv >= AlphaThreshold THEN
                                NewConf(conf[v][i], pref[v][i])
                            ELSE IF nv >= AlphaThreshold THEN
                                NewConf(conf[v][i], ~pref[v][i])
                            ELSE 0]]
            /\ decided' = [decided EXCEPT
                ![v] = [i \in Validators |->
                    IF i \notin Honest \/ decided[v][i] THEN decided[v][i]
                    ELSE LET yv == voteFn[i]
                             nv == K - yv
                             nc == IF yv >= AlphaThreshold THEN
                                       NewConf(conf[v][i], pref[v][i])
                                   ELSE IF nv >= AlphaThreshold THEN
                                       NewConf(conf[v][i], ~pref[v][i])
                                   ELSE 0
                         IN nc >= Beta]]
            /\ decision' = [decision EXCEPT
                ![v] = [i \in Validators |->
                    IF i \notin Honest \/ decided[v][i] THEN decision[v][i]
                    ELSE LET yv == voteFn[i]
                             nv == K - yv
                             nc == IF yv >= AlphaThreshold THEN
                                       NewConf(conf[v][i], pref[v][i])
                                   ELSE IF nv >= AlphaThreshold THEN
                                       NewConf(conf[v][i], ~pref[v][i])
                                   ELSE 0
                         IN IF nc >= Beta THEN
                                IF yv >= AlphaThreshold THEN Accept
                                ELSE Reject
                            ELSE Undecided]]
    /\ round' = round + 1
    /\ UNCHANGED byz

(*
 * ByzantineStep(v):
 *   Byzantine validators set arbitrary local state. They are unconstrained.
 *   They cannot modify honest node state. Their influence on honest nodes
 *   is captured by the nondeterministic voteFn in RoundStep.
 *)
ByzantineStep(v) ==
    /\ byz # {}
    /\ \E i \in byz :
        \E p \in BOOLEAN, c \in 0..Beta, d \in BOOLEAN, r \in Decisions :
            /\ pref'     = [pref     EXCEPT ![v][i] = p]
            /\ conf'     = [conf     EXCEPT ![v][i] = c]
            /\ decided'  = [decided  EXCEPT ![v][i] = d]
            /\ decision' = [decision EXCEPT ![v][i] = r]
    /\ round' = round + 1
    /\ UNCHANGED byz

\* --------------------------------------------------------------------------
\* NEXT-STATE RELATION
\* --------------------------------------------------------------------------

Next ==
    \E v \in Values :
        RoundStep(v) \/ ByzantineStep(v)

\* --------------------------------------------------------------------------
\* FAIRNESS (for liveness checking)
\* --------------------------------------------------------------------------

(*
 * Weak fairness for round steps on each value.
 * Models synchrony: rounds eventually happen for each pending value.
 *)
Fairness ==
    \A v \in Values :
        WF_vars(RoundStep(v))

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ Fairness

\* ==========================================================================
\* SAFETY PROPERTIES
\* ==========================================================================

(*
 * Safety: No two honest validators finalize the same value with conflicting
 * decisions (one Accept, one Reject).
 *
 * Translation of Safety.lean theorem safety (lines 143-158).
 *
 * Proof sketch (why this holds in the model):
 *   Suppose honest i finalizes Accept for v and honest j finalizes Reject.
 *   - i's Accept requires beta consecutive rounds with yesVotes >= alpha.
 *     In each of those rounds, roundDir = "yes" (the only direction that
 *     can produce yesVotes >= alpha).
 *   - j's Reject requires beta consecutive rounds with noVotes >= alpha.
 *     In each of those rounds, roundDir = "no".
 *   - By finalization_windows_overlap (Safety.lean:122-130), the two
 *     beta-length windows share at least one round.
 *   - In that shared round, roundDir was simultaneously "yes" and "no",
 *     which is impossible (roundDir is a single choice per round).
 *   - Contradiction. QED.
 *)
Safety ==
    \A v \in Values :
        \A i, j \in Validators :
            (i \in Honest /\ j \in Honest /\ decided[v][i] /\ decided[v][j])
            => (decision[v][i] = decision[v][j])

(*
 * AgreementOnAccept: No honest Accept and honest Reject for same value.
 *)
AgreementOnAccept ==
    \A v \in Values :
        ~ \E i, j \in Honest :
            /\ decided[v][i] /\ decision[v][i] = Accept
            /\ decided[v][j] /\ decision[v][j] = Reject

(*
 * FinalizedIrrevocable: Decided honest validators never change.
 * Structurally enforced: RoundStep skips decided[v][i]=TRUE validators.
 *)
FinalizedStableAction ==
    \A v \in Values : \A i \in Honest :
        decided[v][i] =>
            /\ decided'[v][i]
            /\ decision'[v][i] = decision[v][i]

\* ==========================================================================
\* LIVENESS PROPERTIES
\* ==========================================================================

(*
 * Liveness: Every honest validator eventually finalizes.
 *
 * With fairness (WF on RoundStep) and nondeterministic roundDir, TLC
 * checks whether all fair infinite behaviors reach finalization.
 *
 * Under pure WF, counterexamples exist (roundDir can alternate forever).
 * Real Snow protocols have probabilistic convergence guarantees.
 * For TLC verification, enable the round bound in Wave.cfg.
 *)
Liveness ==
    \A v \in Values : \A i \in Honest :
        <>(decided[v][i])

\* ==========================================================================
\* AUXILIARY INVARIANTS
\* ==========================================================================

ConfidenceBound ==
    \A v \in Values : \A i \in Validators :
        conf[v][i] <= Beta

DecisionConsistency ==
    \A v \in Values : \A i \in Honest :
        IF decided[v][i]
        THEN decision[v][i] \in {Accept, Reject}
        ELSE decision[v][i] = Undecided

PreferenceMatchesDecision ==
    \A v \in Values : \A i \in Honest :
        /\ (decided[v][i] /\ decision[v][i] = Accept) => pref[v][i]
        /\ (decided[v][i] /\ decision[v][i] = Reject) => ~pref[v][i]

=============================================================================
