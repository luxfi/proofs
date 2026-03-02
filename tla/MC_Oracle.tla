---------------------------- MODULE MC_Oracle ---------------------------------
(*
 * Model Checking Wrapper for Price Oracle
 *
 * Instantiates Oracle.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters:
 *   - 3 updaters: {"u1", "u2", "u3"}
 *   - MinUpdaters = 2 (2-of-3 quorum)
 *   - PriceRange = {8, 9, 10, 11, 12}
 *   - MaxStaleness = 3 ticks
 *   - MaxDeviation = 2 (from current price)
 *   - MaxTime = 8
 *
 * State space: updaters * prices * time bounded by constraints.
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_Oracle.cfg MC_Oracle
 *   Apalache: apalache-mc check --config=MC_Oracle.cfg MC_Oracle.tla
 *)

EXTENDS Oracle

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_Updaters      == {"u1", "u2", "u3"}
MC_PriceRange    == {8, 9, 10, 11, 12}
MC_MinUpdaters   == 2
MC_MaxStaleness  == 3
MC_MaxDeviation  == 2
MC_MaxTime       == 8

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT
\* --------------------------------------------------------------------------

StateConstraint ==
    /\ globalTime <= MC_MaxTime
    /\ roundId <= 4

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK              == TypeOK
MC_FreshnessGuarantee  == FreshnessGuarantee
MC_QuorumRequired      == QuorumRequired
MC_PriceInRange        == PriceInRange
MC_MonotonicRound      == MonotonicRound
MC_MonotonicTime       == MonotonicTime
MC_SubmissionValidity  == SubmissionValidity

=============================================================================
