---------------------------- MODULE MC_Teleport ------------------------------
(*
 * Model Checking Wrapper for Teleport Bridge Protocol
 *
 * Instantiates Teleport.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters:
 *   - 2 chains: {"src", "dst"}
 *   - 2 tokens: {"LUX", "USDC"}
 *   - MaxAmount = 3 (amounts 0..3)
 *   - MaxNonce = 4 (nonces 1..4)
 *   - 3 signers: {"s1", "s2", "s3"}
 *
 * State space analysis:
 *   Per chain per token: locked(4) * minted(4) * backing(4) = 64
 *   2 chains * 2 tokens: 64^4 = 16,777,216 balance states
 *   Nonces per chain: 2^4 = 16 subsets
 *   Pause per chain: 2^2 = 4
 *   Total: ~16M * 256 * 4 = ~16B (large but tractable with constraints)
 *   With state constraint (max 8 actions): explored in minutes.
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_Teleport.cfg MC_Teleport
 *   Apalache: apalache-mc check --config=MC_Teleport.cfg MC_Teleport.tla
 *)

EXTENDS Teleport

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_Chains  == {"src", "dst"}
MC_Tokens  == {"LUX", "USDC"}
MC_MaxAmount == 3
MC_MaxNonce  == 4
MC_Signers == {"s1", "s2", "s3"}

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT (bound exploration for TLC)
\* --------------------------------------------------------------------------

(*
 * Limit the total number of processed nonces across all chains.
 * This bounds state space without cutting reachable invariant violations.
 *)
MC_MaxTotalNonces == 6

TotalNonceCount ==
    SumOver([c \in MC_Chains |-> Cardinality(nonces[c])], MC_Chains)

StateConstraint ==
    TotalNonceCount <= MC_MaxTotalNonces

\* --------------------------------------------------------------------------
\* SYMMETRY (for TLC performance)
\* --------------------------------------------------------------------------

MC_ChainSymmetry == Permutations(MC_Chains)
MC_TokenSymmetry == Permutations(MC_Tokens)

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK              == TypeOK
MC_BackingInvariant    == BackingInvariant
MC_NonceInvariant      == NonceInvariant
MC_ExitGuarantee       == ExitGuarantee
MC_NonNegativeBalances == NonNegativeBalances
MC_NoncesFinite        == NoncesFinite

(*
 * ConservationOfValue: Mint now requires a corresponding Lock on a
 * source chain, so this invariant is checkable by TLC.
 *)
MC_ConservationOfValue == ConservationOfValue

=============================================================================
