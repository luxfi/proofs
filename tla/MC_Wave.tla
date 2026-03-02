---------------------------- MODULE MC_Wave ---------------------------------
(*
 * Model Checking Wrapper for Wave Consensus Protocol
 *
 * Instantiates Wave.tla with concrete constants for tractable model checking.
 *
 * Parameters: N=4, F=1
 *   - 4 validators, at most 1 Byzantine (3*1=3 < 4, so BFT bound holds)
 *   - K=3 (sample 3 of 4 peers)
 *   - AlphaThreshold=3 (all 3 sampled must agree; 3*3=9 > 2*3=6)
 *   - Beta=2 (finalize after 2 consecutive confirming rounds)
 *   - Values={"v1"} (single value to decide)
 *
 * State space analysis:
 *   Per honest validator per value: pref(2) * conf(3) * decided(2) * dec(3) = 36
 *   3 honest validators: 36^3 = 46,656 states per value
 *   1 Byzantine validator: unconstrained but bounded by type (36 states)
 *   Total per value: ~1.7M * subset choices * round bound
 *   With round bound 15: tractable for TLC in minutes.
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config Wave.cfg MC_Wave
 *   Apalache: apalache-mc check --config=Wave.cfg MC_Wave.tla
 *)

EXTENDS Wave

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_N              == 4
MC_F              == 1
MC_K              == 3
MC_AlphaThreshold == 3    \* ceil(0.8 * 3) = 3; satisfies 3*3=9 > 2*3=6
MC_Beta           == 2
MC_Values         == {"v1"}

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT (bound exploration for TLC)
\* --------------------------------------------------------------------------

(*
 * With Beta=2, finalization can happen in 2 rounds. We allow up to
 * MC_RoundBound rounds to explore post-finalization behavior and
 * Byzantine interference patterns.
 *)
MC_RoundBound == 15

StateConstraint ==
    round <= MC_RoundBound

\* --------------------------------------------------------------------------
\* SYMMETRY (for TLC performance with 2+ values)
\* --------------------------------------------------------------------------

MC_Symmetry == Permutations(MC_Values)

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK               == TypeOK
MC_Safety               == Safety
MC_AgreementOnAccept    == AgreementOnAccept
MC_ConfidenceBound      == ConfidenceBound
MC_DecisionConsistency  == DecisionConsistency
MC_PrefMatchesDecision  == PreferenceMatchesDecision

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_FinalizedStable == [][FinalizedStableAction]_vars

(*
 * Liveness under nondeterminism -- will find counterexample.
 * Uncomment in Wave.cfg only to confirm counterexample exists.
 *)
MC_Liveness == Liveness

=============================================================================
