---------------------------- MODULE MC_AMM -----------------------------------
(*
 * Model Checking Wrapper for Constant Product AMM
 *
 * Instantiates AMM.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters:
 *   - 2 addresses: {"a1", "a2"}
 *   - MaxAmount = 10
 *   - FeeNum = 997, FeeDen = 1000 (0.3% fee)
 *
 * State space analysis:
 *   reserve0, reserve1: 0..10 each (11 values)
 *   totalShares: 0..10 (11 values)
 *   shares: 2 addresses * 0..10 = 11^2
 *   k: 0..100
 *   Total: ~11^5 * 100 ~ 1.6M (tractable with constraint)
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_AMM.cfg MC_AMM
 *   Apalache: apalache-mc check --config=MC_AMM.cfg MC_AMM.tla
 *)

EXTENDS AMM

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_Addresses == {"a1", "a2"}
MC_MaxAmount == 10
MC_FeeNum    == 997
MC_FeeDen    == 1000

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT
\* --------------------------------------------------------------------------

StateConstraint ==
    /\ reserve0 <= MC_MaxAmount
    /\ reserve1 <= MC_MaxAmount
    /\ totalShares <= MC_MaxAmount

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK              == TypeOK
MC_ConstantProduct     == ConstantProduct
MC_SharesConsistent    == SharesConsistent
MC_NonNegativeReserves == NonNegativeReserves
MC_NoEmptyPoolWithShares == NoEmptyPoolWithShares

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_KMonotonic == KMonotonic

=============================================================================
