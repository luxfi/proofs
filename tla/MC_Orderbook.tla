---------------------------- MODULE MC_Orderbook ------------------------------
(*
 * Model Checking Wrapper for CLOB Orderbook
 *
 * Instantiates Orderbook.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters:
 *   - 3 order IDs: {"o1", "o2", "o3"}
 *   - MaxPrice = 3
 *   - MaxAmount = 3
 *   - MinFillSize = 1
 *   - MaxFills = 6
 *
 * State space analysis:
 *   Per order: side(2) * price(0..3) * amount(0..3) * filled(0..3)
 *              * seqNo(0..3) * active(2) ~ 512
 *   3 orders: ~134M order states
 *   fills: sequences up to length 6 over fill records
 *   With fill bound: tractable for TLC in minutes.
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_Orderbook.cfg MC_Orderbook
 *   Apalache: apalache-mc check --config=MC_Orderbook.cfg MC_Orderbook.tla
 *)

EXTENDS Orderbook

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_OrderIds    == {"o1", "o2", "o3"}
MC_MaxPrice    == 3
MC_MaxAmount   == 3
MC_MinFillSize == 1
MC_MaxFills    == 6

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT
\* --------------------------------------------------------------------------

StateConstraint ==
    Len(fills) <= MC_MaxFills

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK                     == TypeOK
MC_FillsBounded               == FillsBounded
MC_PriceTimePriorityInvariant == PriceTimePriorityInvariant
MC_NoOverfill                 == NoOverfill
MC_ConsistentFillState        == ConsistentFillState

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_MonotonicFilled      == MonotonicFilled
MC_MonotonicFillsAction == MonotonicFillsAction

=============================================================================
