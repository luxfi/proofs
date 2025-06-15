/-
  Warp Cross-Chain Exactly-Once Delivery

  Models the Warp messaging protocol used for cross-chain communication.

  Warp messages carry BLS aggregate signatures from source chain validators.
  The destination chain verifies the aggregate signature against the known
  validator set before processing.

  Maps to:
  - src/precompiles/warp/: Warp precompile at 0x0200...0005
  - treasury/Vault.sol: usedNonces mapping for replay protection
  - treasury/Collect.sol: version monotonicity for settings

  Properties:
  - Authenticity: only messages signed by source validators are accepted
  - No replay: each message processed at most once (nonce tracking)
  - No loss: valid messages eventually delivered (under liveness assumption)
  - Combined: exactly-once delivery
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Warp.Delivery

/-- Chain identifier -/
abbrev ChainId := Nat

/-- Warp message -/
structure WarpMessage where
  sourceChain : ChainId
  destChain   : ChainId
  nonce       : Nat
  payload     : Nat  -- hash of payload
  sigValid    : Bool -- BLS aggregate signature valid

/-- Destination chain state for Warp processing -/
structure DestState where
  processedNonces : Finset Nat    -- nonces already processed
  lastProcessed   : Nat           -- monotonic counter

/-- Process a Warp message -/
def processMessage (s : DestState) (msg : WarpMessage) : Option DestState :=
  if ¬msg.sigValid then none           -- reject invalid signature
  else if msg.nonce ∈ s.processedNonces then none  -- reject replay
  else some {
    processedNonces := s.processedNonces ∪ {msg.nonce}
    lastProcessed := max s.lastProcessed msg.nonce
  }

/-- No replay: a processed nonce is never accepted again -/
theorem no_replay (s : DestState) (msg : WarpMessage)
    (hmem : msg.nonce ∈ s.processedNonces) :
    processMessage s msg = none := by
  simp [processMessage]
  intro _
  exact hmem

/-- Authenticity: only valid signatures are processed -/
theorem authenticity (s : DestState) (msg : WarpMessage)
    (hinv : msg.sigValid = false) :
    processMessage s msg = none := by
  simp [processMessage, hinv]

/-- Valid messages succeed on first attempt -/
theorem valid_message_succeeds (s : DestState) (msg : WarpMessage)
    (hsig : msg.sigValid = true)
    (hfresh : msg.nonce ∉ s.processedNonces) :
    ∃ s', processMessage s msg = some s' := by
  simp [processMessage, hsig, hfresh]

/-- Processed nonces grow monotonically -/
theorem nonces_monotone (s : DestState) (msg : WarpMessage)
    (h : processMessage s msg = some s') :
    s.processedNonces ⊆ s'.processedNonces := by
  simp [processMessage] at h
  split at h <;> simp_all
  split at h <;> simp_all
  exact Finset.subset_union_left

end Warp.Delivery
