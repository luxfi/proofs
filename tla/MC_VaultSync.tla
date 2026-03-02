---- MODULE MC_VaultSync ----
\* Model checking configuration for VaultSync

EXTENDS VaultSync

\* Small model for exhaustive checking
MC_Devices == {"phone", "laptop"}
MC_MaxOps == 3

====
