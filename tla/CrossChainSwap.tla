---------------------------- MODULE CrossChainSwap ----------------------------
(*
 * TLA+ Specification of the Lux Cross-Chain Swap Protocol
 *
 * Source: ~/work/lux/bridge/
 *
 * Protocol summary:
 *   Cross-chain swaps allow users to atomically exchange tokens between
 *   two chains. The protocol uses a lock-mint-burn-release pattern with
 *   timeouts for safety:
 *
 *   1. User locks tokens on the source chain.
 *   2. Relayer observes the lock and mints wrapped tokens on the destination.
 *   3. On return: user burns wrapped tokens, relayer releases originals.
 *   4. If the destination mint fails or times out, the source lock is reverted.
 *
 *   Each swap carries a unique ID and a deadline. After the deadline,
 *   an unfinished swap can be refunded (source lock reverted).
 *
 * State model:
 *   swaps[id]           -- record per swap
 *     .phase            -- Idle | Locked | Minted | Completed | Refunded
 *     .srcChain         -- source chain
 *     .dstChain         -- destination chain
 *     .amount           -- amount being swapped
 *     .deadline         -- timeout round
 *   srcLocked[c]        -- total tokens locked on source chain c
 *   dstMinted[c]        -- total tokens minted on destination chain c
 *   clock               -- global round counter
 *
 * Safety:
 *   LockBeforeMint      -- mint only after lock
 *   TimeoutRefund       -- if deadline passes without mint, refund enabled
 *   AtomicCompletion    -- mint + lock always paired
 *   ConservationInFlight -- srcLocked = dstMinted + inFlight
 *
 * Liveness:
 *   AllSwapsTerminate    -- every swap reaches Completed or Refunded
 *)

EXTENDS Integers, FiniteSets

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    SwapIds,        \* Set of swap identifiers (e.g. {"s1", "s2"})
    Chains,         \* Set of chain identifiers (e.g. {"src", "dst"})
    MaxAmount,      \* Upper bound on swap amounts
    MaxRound        \* Upper bound on clock for model checking

\* --------------------------------------------------------------------------
\* ASSUMPTIONS
\* --------------------------------------------------------------------------

ASSUME SwapIds # {} /\ IsFiniteSet(SwapIds)
ASSUME Chains # {} /\ IsFiniteSet(Chains)
ASSUME Cardinality(Chains) >= 2
ASSUME MaxAmount \in Nat \ {0}
ASSUME MaxRound \in Nat \ {0}

\* --------------------------------------------------------------------------
\* DERIVED SETS
\* --------------------------------------------------------------------------

Phases == {"Idle", "Locked", "Minted", "Completed", "Refunded"}
TerminalPhases == {"Completed", "Refunded"}
Amounts == 0..MaxAmount

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    swaps,          \* swaps[id] = [phase, srcChain, dstChain, amount, deadline]
    srcLocked,      \* srcLocked[c] \in Nat -- total locked on chain c
    dstMinted,      \* dstMinted[c] \in Nat -- total minted on chain c
    clock           \* global round counter

vars == <<swaps, srcLocked, dstMinted, clock>>

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

SwapType ==
    [phase    : Phases,
     srcChain : Chains,
     dstChain : Chains,
     amount   : Amounts,
     deadline : 0..MaxRound]

TypeOK ==
    /\ swaps \in [SwapIds -> SwapType]
    /\ srcLocked \in [Chains -> Nat]
    /\ dstMinted \in [Chains -> Nat]
    /\ clock \in 0..MaxRound

\* --------------------------------------------------------------------------
\* HELPERS
\* --------------------------------------------------------------------------

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + SumOver(f, S \ {x})

TotalSrcLocked == SumOver(srcLocked, Chains)
TotalDstMinted == SumOver(dstMinted, Chains)

\* In-flight: swaps that are Locked but not yet Minted, Completed, or Refunded
InFlightAmount ==
    SumOver(
        [id \in SwapIds |-> IF swaps[id].phase = "Locked"
                            THEN swaps[id].amount ELSE 0],
        SwapIds)

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ swaps = [id \in SwapIds |->
        [phase    |-> "Idle",
         srcChain |-> CHOOSE c \in Chains : TRUE,
         dstChain |-> CHOOSE c \in Chains : TRUE,
         amount   |-> 0,
         deadline |-> 0]]
    /\ srcLocked = [c \in Chains |-> 0]
    /\ dstMinted = [c \in Chains |-> 0]
    /\ clock = 0

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

(*
 * Tick:
 *   Advance the global clock.
 *)
Tick ==
    /\ clock < MaxRound
    /\ clock' = clock + 1
    /\ UNCHANGED <<swaps, srcLocked, dstMinted>>

(*
 * InitiateSwap(id, src, dst, amt):
 *   User initiates a cross-chain swap. Locks tokens on source chain.
 *   Sets a deadline for the swap to complete.
 *)
InitiateSwap(id, src, dst, amt) ==
    /\ swaps[id].phase = "Idle"
    /\ src # dst
    /\ amt > 0
    /\ srcLocked[src] + amt <= MaxAmount
    /\ clock + 2 <= MaxRound   \* need at least 2 rounds for mint + complete
    /\ swaps' = [swaps EXCEPT ![id] =
        [phase    |-> "Locked",
         srcChain |-> src,
         dstChain |-> dst,
         amount   |-> amt,
         deadline |-> clock + 2]]
    /\ srcLocked' = [srcLocked EXCEPT ![src] = @ + amt]
    /\ UNCHANGED <<dstMinted, clock>>

(*
 * MintOnDest(id):
 *   Relayer mints wrapped tokens on destination chain.
 *   Precondition: swap is Locked, deadline not passed.
 *)
MintOnDest(id) ==
    /\ swaps[id].phase = "Locked"
    /\ clock < swaps[id].deadline
    /\ dstMinted[swaps[id].dstChain] + swaps[id].amount <= MaxAmount
    /\ swaps' = [swaps EXCEPT ![id] = [@ EXCEPT !.phase = "Minted"]]
    /\ dstMinted' = [dstMinted EXCEPT ![swaps[id].dstChain] = @ + swaps[id].amount]
    /\ UNCHANGED <<srcLocked, clock>>

(*
 * CompleteSwap(id):
 *   Swap completes. Source lock becomes permanent backing for the mint.
 *)
CompleteSwap(id) ==
    /\ swaps[id].phase = "Minted"
    /\ swaps' = [swaps EXCEPT ![id] = [@ EXCEPT !.phase = "Completed"]]
    /\ UNCHANGED <<srcLocked, dstMinted, clock>>

(*
 * RefundSwap(id):
 *   Deadline passed without mint completing. Refund the source lock.
 *   Also handles the case where mint happened but completion failed:
 *   in that case the destination mint is also reverted.
 *)
RefundSwap(id) ==
    /\ swaps[id].phase \in {"Locked", "Minted"}
    /\ clock >= swaps[id].deadline
    /\ LET src == swaps[id].srcChain
           dst == swaps[id].dstChain
           amt == swaps[id].amount
           wasMinted == swaps[id].phase = "Minted"
       IN /\ srcLocked' = [srcLocked EXCEPT ![src] = @ - amt]
          /\ dstMinted' = IF wasMinted
                          THEN [dstMinted EXCEPT ![dst] = @ - amt]
                          ELSE dstMinted
          /\ swaps' = [swaps EXCEPT ![id] = [@ EXCEPT !.phase = "Refunded"]]
    /\ UNCHANGED clock

\* --------------------------------------------------------------------------
\* NEXT-STATE RELATION
\* --------------------------------------------------------------------------

Next ==
    \/ Tick
    \/ \E id \in SwapIds, src, dst \in Chains, amt \in 1..MaxAmount :
        InitiateSwap(id, src, dst, amt)
    \/ \E id \in SwapIds : MintOnDest(id)
    \/ \E id \in SwapIds : CompleteSwap(id)
    \/ \E id \in SwapIds : RefundSwap(id)

\* --------------------------------------------------------------------------
\* FAIRNESS
\* --------------------------------------------------------------------------

Fairness ==
    /\ WF_vars(Tick)
    /\ \A id \in SwapIds : WF_vars(RefundSwap(id))
    /\ \A id \in SwapIds : WF_vars(CompleteSwap(id))

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ Fairness

\* ==========================================================================
\* SAFETY INVARIANTS
\* ==========================================================================

(*
 * LockBeforeMint:
 *   A swap can only be Minted if it was previously Locked.
 *   Tokens must be locked on source before minting on destination.
 *   Enforced structurally: MintOnDest requires phase = "Locked".
 *
 *   We verify: for any Minted or Completed swap, srcLocked >= amount.
 *)
LockBeforeMint ==
    \A id \in SwapIds :
        swaps[id].phase \in {"Minted", "Completed"}
        => srcLocked[swaps[id].srcChain] >= swaps[id].amount

(*
 * TimeoutRefund:
 *   If a swap's deadline has passed and it is not Completed,
 *   refund is enabled. Users can always get their tokens back.
 *)
TimeoutRefund ==
    \A id \in SwapIds :
        (swaps[id].phase \in {"Locked", "Minted"} /\ clock >= swaps[id].deadline)
        => ENABLED RefundSwap(id)

(*
 * ConservationInvariant:
 *   Total locked on all source chains = total minted on all destinations
 *   plus the in-flight amount (locked but not yet minted).
 *)
ConservationInvariant ==
    TotalSrcLocked = TotalDstMinted + InFlightAmount

(*
 * NoNegativeBalances:
 *   Locked and minted totals are non-negative.
 *)
NoNegativeBalances ==
    /\ \A c \in Chains : srcLocked[c] >= 0
    /\ \A c \in Chains : dstMinted[c] >= 0

(*
 * PhaseConsistency:
 *   Terminal swaps (Completed, Refunded) never change phase.
 *)
PhaseStable ==
    [][
        \A id \in SwapIds :
            swaps[id].phase \in TerminalPhases
            => swaps'[id].phase = swaps[id].phase
    ]_vars

\* ==========================================================================
\* LIVENESS PROPERTIES
\* ==========================================================================

(*
 * AllSwapsTerminate:
 *   Every initiated swap eventually reaches Completed or Refunded.
 *   Under fairness (Tick + RefundSwap + CompleteSwap are weakly fair),
 *   the clock advances, deadlines are reached, and refunds fire.
 *)
AllSwapsTerminate ==
    \A id \in SwapIds :
        (swaps[id].phase = "Locked")
        ~> (swaps[id].phase \in TerminalPhases)

=============================================================================
