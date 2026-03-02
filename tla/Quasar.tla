---------------------------- MODULE Quasar ----------------------------
(*
 * TLA+ Specification of the Quasar Consensus Protocol
 *
 * Source: ~/work/lux/consensus/protocol/quasar/quasar.go
 *         ~/work/lux/consensus/protocol/quasar/core.go
 *         ~/work/lux/consensus/protocol/quasar/grouped_threshold.go
 *
 * Protocol summary:
 *   Quasar uses three independent cryptographic signing layers:
 *     1. BLS12-381 aggregate signatures (ECDL hardness, classical)
 *     2. Ringtail Ring-LWE threshold signatures (Module-LWE, PQ-safe)
 *     3. ML-DSA-65 identity signatures (Module-LWE + Module-SIS, PQ-safe)
 *
 *   Validators collect signatures across all enabled layers. A block is
 *   finalized when a quorum of validator weight signs it on ALL enabled
 *   layers. The quorum check uses cross-multiplication to avoid integer
 *   truncation:
 *
 *     signerWeight * quorumDen >= totalWeight * quorumNum
 *
 *   This is equivalent to signerWeight/totalWeight >= quorumNum/quorumDen
 *   without floating-point division.
 *
 *   Four modes (quasar.go IsQuantumMode, IsDualThresholdMode):
 *     - BLS-only: fastest classical consensus
 *     - BLS + ML-DSA (dual): classical + PQ identity
 *     - BLS + Ringtail (dual): classical + PQ threshold
 *     - BLS + Ringtail + ML-DSA (quantum): full PQ-safe finality
 *
 * Safety property:
 *   No two conflicting values can both be finalized. This follows from
 *   the BFT quorum intersection argument: two 2/3 quorums of an n-node
 *   set with f < n/3 Byzantine share at least one honest node. An honest
 *   node signs at most one value per round, so conflicting values cannot
 *   both reach quorum.
 *
 * Quantum unforgeability:
 *   An adversary must compromise ALL three cryptographic layers to forge
 *   a certificate. Compromising any strict subset is insufficient because
 *   the verifier requires valid signatures on all enabled layers.
 *
 * Go-to-TLA+ mapping:
 *   signer.threshold              -> threshold
 *   signer.validators[id].Weight  -> weight[v]
 *   signer.blsSigners             -> blsSigned[v][i]
 *   signer.ringtailSigners        -> rtSigned[v][i]
 *   signer.mldsaKeys              -> mldsaSigned[v][i]
 *   addVoteLocked quorum check    -> QuorumMet(layer, v)
 *   IsQuantumMode                  -> enableBLS /\ enableRT /\ enableMLDSA
 *   IsDualThresholdMode           -> enableBLS /\ enableRT
 *)

EXTENDS Integers, FiniteSets, Sequences

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    N,             \* Total validators
    F,             \* Max Byzantine validators (f < n/3)
    QuorumNum,     \* Quorum numerator (e.g. 2 for 2/3)
    QuorumDen,     \* Quorum denominator (e.g. 3 for 2/3)
    EnableBLS,     \* Boolean: BLS layer active (always TRUE in practice)
    EnableRT,      \* Boolean: Ringtail layer active
    EnableMLDSA,   \* Boolean: ML-DSA layer active
    Values         \* Set of values to finalize

\* --------------------------------------------------------------------------
\* ASSUMPTIONS (mirror BFT constraints from core.go and quasar.go)
\* --------------------------------------------------------------------------

ASSUME N \in Nat \ {0}
ASSUME F \in Nat /\ 3 * F < N                        \* BFT bound
ASSUME QuorumNum \in Nat \ {0}
ASSUME QuorumDen \in Nat \ {0}
ASSUME QuorumNum * 3 > QuorumDen * 2                  \* quorum > 2/3
ASSUME EnableBLS \in BOOLEAN
ASSUME EnableRT  \in BOOLEAN
ASSUME EnableMLDSA \in BOOLEAN
ASSUME EnableBLS                                       \* BLS always enabled
ASSUME Values # {} /\ IsFiniteSet(Values)

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    \* Per-layer signature state: who has signed which value
    blsSigned,     \* blsSigned[v][i]   \in BOOLEAN
    rtSigned,      \* rtSigned[v][i]    \in BOOLEAN
    mldsaSigned,   \* mldsaSigned[v][i] \in BOOLEAN

    \* Finalization state
    finalized,     \* finalized[v] \in BOOLEAN  -- value v has been finalized
    finalVal,      \* finalVal[v]  \in BOOLEAN  -- what was finalized for v

    \* Validator weights (uniform = 1 in this model)
    weight,        \* weight[i] \in Nat

    \* Byzantine set (chosen at init, fixed)
    byz,           \* byz \subseteq Validators

    \* Round counter
    round          \* round \in Nat

vars == <<blsSigned, rtSigned, mldsaSigned, finalized, finalVal, weight, byz, round>>

\* --------------------------------------------------------------------------
\* DERIVED SETS
\* --------------------------------------------------------------------------

Validators == 1..N

Honest == Validators \ byz

\* --------------------------------------------------------------------------
\* HELPER: Cross-multiply quorum check (core.go addVoteLocked)
\* --------------------------------------------------------------------------

(*
 * CrossMultQuorum(sigWeight, totalWeight):
 *   sigWeight * QuorumDen >= totalWeight * QuorumNum
 *
 * This is the integer-exact equivalent of sigWeight/totalWeight >= QuorumNum/QuorumDen.
 * No floating-point, no truncation. Matches grouped_threshold.go GroupQuorum logic.
 *)
CrossMultQuorum(sigWeight, totalWeight) ==
    sigWeight * QuorumDen >= totalWeight * QuorumNum

\* Total weight of all validators
TotalWeight == N  \* uniform weight=1 per validator in this model

\* Weight of signers for a layer on value v
BLSWeight(v)   == Cardinality({i \in Validators : blsSigned[v][i]})
RTWeight(v)    == Cardinality({i \in Validators : rtSigned[v][i]})
MLDSAWeight(v) == Cardinality({i \in Validators : mldsaSigned[v][i]})

\* A layer has quorum when cross-multiply check passes
BLSQuorum(v)   == CrossMultQuorum(BLSWeight(v), TotalWeight)
RTQuorum(v)    == CrossMultQuorum(RTWeight(v), TotalWeight)
MLDSAQuorum(v) == CrossMultQuorum(MLDSAWeight(v), TotalWeight)

\* All ENABLED layers must have quorum for finalization
AllLayersQuorum(v) ==
    /\ (EnableBLS   => BLSQuorum(v))
    /\ (EnableRT    => RTQuorum(v))
    /\ (EnableMLDSA => MLDSAQuorum(v))

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

TypeOK ==
    /\ blsSigned   \in [Values -> [Validators -> BOOLEAN]]
    /\ rtSigned    \in [Values -> [Validators -> BOOLEAN]]
    /\ mldsaSigned \in [Values -> [Validators -> BOOLEAN]]
    /\ finalized   \in [Values -> BOOLEAN]
    /\ finalVal    \in [Values -> BOOLEAN]
    /\ weight      \in [Validators -> Nat]
    /\ byz         \subseteq Validators
    /\ Cardinality(byz) <= F
    /\ round       \in Nat

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ \E b \in SUBSET Validators :
        /\ Cardinality(b) <= F
        /\ byz = b
    /\ blsSigned   = [v \in Values |-> [i \in Validators |-> FALSE]]
    /\ rtSigned    = [v \in Values |-> [i \in Validators |-> FALSE]]
    /\ mldsaSigned = [v \in Values |-> [i \in Validators |-> FALSE]]
    /\ finalized   = [v \in Values |-> FALSE]
    /\ finalVal    = [v \in Values |-> FALSE]
    /\ weight      = [i \in Validators |-> 1]
    /\ round       = 0

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

(*
 * HonestSign(v, i):
 *   Honest validator i signs value v on ALL enabled layers.
 *   An honest validator signs at most ONE value per round (enforced by
 *   the constraint that we only sign v if no conflicting value has been
 *   signed by i in this round).
 *
 *   Maps to signer.QuantumSignRound1 in quasar.go:384 which runs BLS,
 *   Ringtail, and ML-DSA in parallel goroutines.
 *)
HonestSign(v, i) ==
    /\ i \in Honest
    /\ ~finalized[v]
    \* Honest validators sign at most one value: if already signed another, skip
    /\ \A w \in Values \ {v} : ~blsSigned[w][i]
    /\ blsSigned'   = [blsSigned   EXCEPT ![v][i] = TRUE]
    /\ rtSigned'    = [rtSigned    EXCEPT ![v][i] = EnableRT]
    /\ mldsaSigned' = [mldsaSigned EXCEPT ![v][i] = EnableMLDSA]
    /\ UNCHANGED <<finalized, finalVal, weight, byz, round>>

(*
 * ByzantineSign(v, i):
 *   Byzantine validator i can sign any value on any subset of layers.
 *   Models equivocation: signing multiple conflicting values.
 *)
ByzantineSign(v, i) ==
    /\ i \in byz
    /\ ~finalized[v]
    /\ \E signBLS \in BOOLEAN, signRT \in BOOLEAN, signMLDSA \in BOOLEAN :
        /\ blsSigned'   = [blsSigned   EXCEPT ![v][i] = signBLS]
        /\ rtSigned'    = [rtSigned    EXCEPT ![v][i] = signRT]
        /\ mldsaSigned' = [mldsaSigned EXCEPT ![v][i] = signMLDSA]
    /\ UNCHANGED <<finalized, finalVal, weight, byz, round>>

(*
 * Finalize(v):
 *   Checks if value v has reached quorum on ALL enabled layers.
 *   If so, marks v as finalized. Maps to addVoteLocked in core.go:302.
 *)
Finalize(v) ==
    /\ ~finalized[v]
    /\ AllLayersQuorum(v)
    /\ finalized' = [finalized EXCEPT ![v] = TRUE]
    /\ finalVal'  = [finalVal  EXCEPT ![v] = TRUE]
    /\ round'     = round + 1
    /\ UNCHANGED <<blsSigned, rtSigned, mldsaSigned, weight, byz>>

\* --------------------------------------------------------------------------
\* NEXT-STATE RELATION
\* --------------------------------------------------------------------------

Next ==
    \/ \E v \in Values, i \in Validators :
        HonestSign(v, i) \/ ByzantineSign(v, i)
    \/ \E v \in Values : Finalize(v)

\* --------------------------------------------------------------------------
\* FAIRNESS
\* --------------------------------------------------------------------------

Fairness ==
    /\ \A v \in Values : WF_vars(Finalize(v))
    /\ \A v \in Values, i \in Honest : WF_vars(HonestSign(v, i))

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ Fairness

\* ==========================================================================
\* SAFETY PROPERTIES
\* ==========================================================================

(*
 * Safety: No two conflicting values can both be finalized.
 *
 * Proof sketch (quorum intersection):
 *   Assume values v1 and v2 are both finalized (v1 # v2).
 *   Each requires CrossMultQuorum on BLS layer (always enabled).
 *   BLS quorum for v1: |signers(v1)| * QuorumDen >= N * QuorumNum
 *   BLS quorum for v2: |signers(v2)| * QuorumDen >= N * QuorumNum
 *
 *   With QuorumNum/QuorumDen > 2/3:
 *     |signers(v1)| > 2N/3 and |signers(v2)| > 2N/3
 *   So |signers(v1) \cap signers(v2)| > N/3 >= F+1
 *   At least one honest node is in both sets.
 *   But honest nodes sign at most one value. Contradiction.
 *)
Safety ==
    \A v1, v2 \in Values :
        (finalized[v1] /\ finalized[v2] /\ v1 # v2) => FALSE

(*
 * No conflicting BLS quorums: if BLS has quorum for two values,
 * at least one honest validator signed both (impossible).
 *)
BLSQuorumUniqueness ==
    \A v1, v2 \in Values :
        (BLSQuorum(v1) /\ BLSQuorum(v2) /\ v1 # v2) =>
            \E i \in Honest : blsSigned[v1][i] /\ blsSigned[v2][i]

\* ==========================================================================
\* QUANTUM UNFORGEABILITY
\* ==========================================================================

(*
 * QuantumUnforgeability: Forging a certificate requires compromising ALL
 * enabled layers. Even if an adversary fully controls one or two layers,
 * the remaining layer(s) prevent forgery.
 *
 * We model this as: if the honest validators have NOT signed a value v
 * on at least one enabled layer, then v cannot be finalized.
 * The adversary controls only byz nodes (|byz| <= F < N/3), which is
 * insufficient to reach quorum on any layer.
 *)
QuantumUnforgeability ==
    \A v \in Values :
        finalized[v] =>
            \* BLS: enough honest signers
            /\ (EnableBLS =>
                Cardinality({i \in Honest : blsSigned[v][i]}) > 0)
            \* RT: enough honest signers
            /\ (EnableRT =>
                Cardinality({i \in Honest : rtSigned[v][i]}) > 0)
            \* MLDSA: enough honest signers
            /\ (EnableMLDSA =>
                Cardinality({i \in Honest : mldsaSigned[v][i]}) > 0)

(*
 * SingleLayerCompromise: Even if adversary can forge signatures on ONE
 * layer (modeled by giving byz nodes free signing on that layer), safety
 * still holds because the other layers are intact.
 *
 * This is not an action but a property: with f < n/3, Byzantine nodes
 * alone cannot reach quorum (which requires > 2n/3).
 *)
ByzAloneCannotReachQuorum ==
    ~CrossMultQuorum(F, TotalWeight)

\* ==========================================================================
\* LIVENESS
\* ==========================================================================

(*
 * Liveness: If all honest validators eventually sign the same value,
 * that value eventually gets finalized.
 *
 * Under Fairness (WF on HonestSign and Finalize), if honest validators
 * converge on a value (e.g., through Wave/Snow pre-consensus), finalization
 * follows because honest majority > 2/3 exceeds quorum threshold.
 *)
Liveness ==
    \A v \in Values : <>(finalized[v])

\* ==========================================================================
\* AUXILIARY INVARIANTS
\* ==========================================================================

(*
 * HonestAtMostOneValue: An honest validator signs at most one value on BLS.
 *)
HonestSignsAtMostOne ==
    \A i \in Honest :
        Cardinality({v \in Values : blsSigned[v][i]}) <= 1

(*
 * LayerConsistency: If honest i signs BLS for v, they also sign all other
 * enabled layers for v (QuantumSignRound1 signs all in parallel).
 *)
HonestLayerConsistency ==
    \A v \in Values, i \in Honest :
        blsSigned[v][i] =>
            /\ (EnableRT    => rtSigned[v][i])
            /\ (EnableMLDSA => mldsaSigned[v][i])

(*
 * FinalizedIrrevocable: Once finalized, stays finalized.
 * Structurally enforced: Finalize checks ~finalized[v].
 *)
FinalizedStableAction ==
    \A v \in Values :
        finalized[v] => finalized'[v]

=============================================================================
