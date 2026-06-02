---------------------------- MODULE MC_DAGEVM ----------------------------
EXTENDS DAGEVM

\* Small-model instantiation for TLC. See MC_DAGEVM.cfg for constants.

\* State-space bound for tractable checking. Each vertex ranges over a rich
\* structure (reads/writes are subsets of Keys, parents subsets of VertexId),
\* so the set `accepted` blows up combinatorially. Capping it keeps the model
\* finite *and* small while still exercising every property: conflict and
\* antichain checks need >= 2 same-rank vertices, and serializability/rank
\* finalisation need >= 2 ranks -- all reachable within this bound.
StateConstraint ==
    Cardinality(accepted) <= 3
================================================================================
