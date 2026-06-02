---------------------------- MODULE MC_DAGZChain ----------------------------
EXTENDS DAGZChain

\* Small-model instantiation for TLC. See MC_DAGZChain.cfg.

\* State-space bound for tractable checking. Vertices carry subset-valued
\* nullifier/commitment fields, so `accepted` blows up combinatorially.
\* Capping it keeps the model finite and small while still exercising every
\* property: NoDoubleSpend / AntichainDisjoint need >= 2 vertices and the rank
\* finalisation liveness needs >= 2 ranks -- both reachable within this bound.
StateConstraint ==
    Cardinality(accepted) <= 3
================================================================================
