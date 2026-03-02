---------------------------- MODULE MC_CrossChainSwap -------------------------
(*
 * Model Checking Wrapper for Cross-Chain Swap Protocol
 *
 * Instantiates CrossChainSwap.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters:
 *   - 2 swaps: {"s1", "s2"}
 *   - 2 chains: {"src", "dst"}
 *   - MaxAmount = 3
 *   - MaxRound = 6
 *
 * State space analysis:
 *   Per swap: phase(5) * src(2) * dst(2) * amount(0..3) * deadline(0..6) ~ 560
 *   2 swaps: ~300K swap states
 *   srcLocked/dstMinted: 2 chains * 0..3 = 4^2 = 16 each
 *   Total: ~300K * 256 * 7 ~ 500M (tractable with round bound)
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_CrossChainSwap.cfg MC_CrossChainSwap
 *   Apalache: apalache-mc check --config=MC_CrossChainSwap.cfg MC_CrossChainSwap.tla
 *)

EXTENDS CrossChainSwap

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_SwapIds   == {"s1", "s2"}
MC_Chains    == {"src", "dst"}
MC_MaxAmount == 3
MC_MaxRound  == 6

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT
\* --------------------------------------------------------------------------

StateConstraint ==
    clock <= MC_MaxRound

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK                == TypeOK
MC_LockBeforeMint        == LockBeforeMint
MC_ConservationInvariant == ConservationInvariant
MC_NoNegativeBalances    == NoNegativeBalances

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_PhaseStable == PhaseStable

=============================================================================
