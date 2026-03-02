---------------------------- MODULE MC_Quasar -------------------------
(*
 * Model Checking Wrapper for Quasar Consensus Protocol
 *
 * Instantiates Quasar.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters: N=4, F=1
 *   - 4 validators, at most 1 Byzantine (3*1=3 < 4)
 *   - QuorumNum=2, QuorumDen=3 (2/3 quorum, standard BFT)
 *     Quorum check: sigWeight * 3 >= 4 * 2 = 8, so need sigWeight >= 3
 *     With 1 Byzantine, honest can contribute 3. Meets quorum.
 *   - All three layers enabled (quantum mode)
 *   - Two values to decide (tests conflict detection)
 *
 * State space analysis:
 *   Per validator per value per layer: 2 (signed or not)
 *   3 layers * 4 validators * 2 values = 24 boolean vars
 *   Plus finalized[2], finalVal[2], byz(subset of 4), round
 *   Total: ~2^24 * 16 * bound ~ tractable with round bound 8
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_Quasar.cfg MC_Quasar
 *   Apalache: apalache-mc check --config=MC_Quasar.cfg MC_Quasar.tla
 *)

EXTENDS Quasar

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_N          == 4
MC_F          == 1
MC_QuorumNum  == 2
MC_QuorumDen  == 3
MC_EnableBLS  == TRUE
MC_EnableRT   == TRUE
MC_EnableMLDSA == TRUE
MC_Values     == {"v1", "v2"}

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT (bound exploration for TLC)
\* --------------------------------------------------------------------------

MC_RoundBound == 8

StateConstraint ==
    round <= MC_RoundBound

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK                    == TypeOK
MC_Safety                    == Safety
MC_QuantumUnforgeability      == QuantumUnforgeability
MC_ByzAloneCannotReachQuorum == ByzAloneCannotReachQuorum
MC_HonestSignsAtMostOne      == HonestSignsAtMostOne
MC_HonestLayerConsistency    == HonestLayerConsistency

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_FinalizedStable == [][FinalizedStableAction]_vars

\* Liveness will produce counterexamples because honest nodes may never
\* converge on a single value under pure nondeterminism. This is expected;
\* Wave/Snow pre-consensus provides probabilistic convergence.
\* Uncomment in .cfg to verify the counterexample exists:
MC_Liveness == Liveness

\* --------------------------------------------------------------------------
\* SYMMETRY (reduces state space for 2+ values)
\* --------------------------------------------------------------------------

MC_Symmetry == Permutations(MC_Values)

=============================================================================
