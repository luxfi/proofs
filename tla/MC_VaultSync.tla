---- MODULE MC_VaultSync ----
\* Model checking configuration for VaultSync

EXTENDS VaultSync

\* Small model for exhaustive checking.
\* Two keys and two values suffice: Convergence only distinguishes whether
\* two devices hold equal vs unequal localState, so >=2 distinct values
\* (to express divergence) over >=2 keys fully exercises it. Larger
\* key/value domains only multiply the localState/oplog space without
\* reaching new control behaviour, so they are bounded here to keep the
\* model exhaustively checkable.
MC_Devices == {"phone", "laptop"}
MC_MaxOps == 3
MC_Keys == {"a", "b"}
MC_Values == {1, 2}

====
