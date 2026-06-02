---------------------------- MODULE MC_StrictPQProfile -------------------------
EXTENDS StrictPQProfile

\* All constants (including NULL) are bound directly in MC_StrictPQProfile.cfg.
\* NULL is the placeholder model value for "no active profile"; the base-spec
\* ASSUME NULL \notin Profiles guarantees it is distinct from every profile id.

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT (bounds the state space for tractable checking)
\* --------------------------------------------------------------------------
\* AdmitTx appends to admittedTxSchemes without advancing height, so without
\* a bound the admitted-tx sequence grows without limit and TLC never
\* terminates (every longer sequence is a new distinct state). Bounding both
\* schedule sequences to MaxHeight keeps exploration finite; signedBlockSchemes
\* is already height-aligned, and MaxHeight admitted txs is ample to exercise
\* the scheme gate.
StateConstraint ==
    /\ Len(admittedTxSchemes) <= MaxHeight
    /\ Len(signedBlockSchemes) <= MaxHeight

============================================================================
