---------------------------- MODULE MC_LiquidStaking -------------------------
(*
 * Model Checking Wrapper for Liquid Staking Protocol
 *
 * Instantiates LiquidStaking.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters:
 *   - 2 addresses: {"a1", "a2"}
 *   - MaxAmount = 10
 *   - Precision = 100 (share price scaled to 2 decimal places)
 *
 * State space analysis:
 *   totalAssets: 0..10 (11 values)
 *   totalShares: 0..10 (11 values)
 *   userShares: 2 addresses * 0..10 = 11^2
 *   lastSharePrice: 0..1000 (bounded by Precision * MaxAmount)
 *   slashingOccurred: 2
 *   Total: ~11^4 * 1000 * 2 ~ 29M (tractable with constraint)
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_LiquidStaking.cfg MC_LiquidStaking
 *   Apalache: apalache-mc check --config=MC_LiquidStaking.cfg MC_LiquidStaking.tla
 *)

EXTENDS LiquidStaking

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_Addresses == {"a1", "a2"}
MC_MaxAmount == 10
MC_Precision == 100

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT
\* --------------------------------------------------------------------------

StateConstraint ==
    /\ totalAssets <= MC_MaxAmount
    /\ totalShares <= MC_MaxAmount

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK              == TypeOK
MC_SharesConsistent    == SharesConsistent
MC_SharePriceMonotonic == SharePriceMonotonic
MC_NonNegativeAssets   == NonNegativeAssets
MC_VaultSolvent        == VaultSolvent

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_SlashingAction == SlashingActionProperty

=============================================================================
