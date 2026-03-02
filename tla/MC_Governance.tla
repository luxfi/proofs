---------------------------- MODULE MC_Governance -----------------------------
(*
 * Model Checking Wrapper for Governance Protocol
 *
 * Instantiates Governance.tla with concrete constants for tractable
 * model checking.
 *
 * Parameters:
 *   - 2 proposals: {"p1", "p2"}
 *   - 3 addresses: {"a1", "a2", "a3"}
 *   - MaxWeight = 2 (voting power 0..2)
 *   - Quorum = 3 (at least 3 total vote weight)
 *   - VotingDuration = 2 (2 rounds of voting)
 *   - MaxRound = 8
 *
 * State space analysis:
 *   Per proposal: state(7) * forVotes(0..6) * againstVotes(0..6)
 *                 * voters(2^3=8) * votingEndsAt(0..8) ~ 28K
 *   2 proposals: ~800M (constrained by round bound and state transitions)
 *   With round bound 8: explored in seconds.
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_Governance.cfg MC_Governance
 *   Apalache: apalache-mc check --config=MC_Governance.cfg MC_Governance.tla
 *)

EXTENDS Governance

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_Proposals       == {"p1", "p2"}
MC_Addresses       == {"a1", "a2", "a3"}
MC_MaxWeight       == 2
MC_Quorum          == 3
MC_VotingDuration  == 2
MC_MaxRound        == 8

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT
\* --------------------------------------------------------------------------

StateConstraint ==
    clock <= MC_MaxRound

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK                  == TypeOK
MC_NoExecuteWithoutQuorum  == NoExecuteWithoutQuorum
MC_NoDoubleVoting          == NoDoubleVoting
MC_VoteWeightBound         == VoteWeightBound
MC_VoteTotalBound          == VoteTotalBound
MC_StateTransitionValidity == StateTransitionValidity

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_NoVoteAfterTally == NoVoteAfterTally

=============================================================================
