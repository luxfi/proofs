---------------------------- MODULE MC_StrictPQProfile -------------------------
EXTENDS StrictPQProfile

CONSTANTS
    NULL_CONST    \* the NULL placeholder for activeProfile

\* Model values bound at TLC time via .cfg
ASSUME NULL_CONST \notin Profiles

============================================================================
