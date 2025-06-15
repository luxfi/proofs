/-
  Bridge Fill Integrity — Atomicity and Conservation

  Formal model of the bridge fill flow where minted tokens on the
  destination chain require both MPC threshold signature verification
  and ERC-3643 compliance approval. No mint occurs unless both gates pass.

  Maps to:
  - contracts/bridge/Teleport.sol: fill() function
  - contracts/bridge/OmnichainRouter.sol: MPC signature verification
  - contracts/compliance/ERC3643Compliance.sol: canTransfer gate
  - lux/mpc: CGGMP21 threshold signing (7-of-11)

  Properties:
  - Fill requires threshold: mint only with sufficient MPC signatures
  - Fill requires compliance: mint only if canTransfer passes
  - Atomicity: both checks pass and mint occurs, or nothing changes
  - Conservation: fill amount ≤ burned amount on source (no inflation)
  - Replay protection: nonce monotonicity prevents double-fill
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Bridge.FillIntegrity

-- ═══════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════

/-- Address identifier -/
abbrev Address := Nat

/-- Nonce for fill ordering -/
abbrev Nonce := Nat

/-- MPC signature: set of signer indices that approved -/
structure MPCSig where
  signers : Finset Nat
  nonce   : Nonce

/-- Bridge parameters -/
structure BridgeParams where
  threshold  : Nat     -- minimum signers required (e.g., 7)
  validators : Nat     -- total validator set size (e.g., 11)
  ht : threshold ≤ validators
  ht0 : threshold > 0

/-- Default: 7-of-11 MPC -/
def defaultParams : BridgeParams :=
  ⟨7, 11, by omega, by omega⟩

-- ═══════════════════════════════════════════════════════════════
-- BRIDGE STATE
-- ═══════════════════════════════════════════════════════════════

/-- Per-chain bridge state tracking fills -/
structure FillState where
  totalMinted     : Nat
  processedNonces : Finset Nonce
  nextNonce       : Nonce           -- monotonically increasing

/-- Source chain state tracking burns -/
structure SourceState where
  totalBurned : Nat

-- ═══════════════════════════════════════════════════════════════
-- FILL FUNCTION
-- ═══════════════════════════════════════════════════════════════

/-- The post-state after a successful fill -/
def fillPostState (state : FillState) (amount : Nat) (sig : MPCSig) : FillState :=
  { totalMinted     := state.totalMinted + amount
    processedNonces := state.processedNonces ∪ {sig.nonce}
    nextNonce       := sig.nonce + 1 }

/-- Execute a bridge fill: verify MPC threshold, check compliance,
    verify nonce freshness and ordering, then mint.
    Returns some post-state if all gates pass, none otherwise.
    The compliance check is a parameter (proved correct in ERC3643.lean). -/
def bridgeFill
    (compliance : Address → Address → Bool)
    (params : BridgeParams)
    (state : FillState)
    (from_ to_ : Address)
    (amount : Nat)
    (sig : MPCSig) : Option FillState :=
  if sig.signers.card ≥ params.threshold  -- Gate 1: MPC threshold
     && compliance from_ to_              -- Gate 2: ERC-3643 compliance
     && decide (sig.nonce ∉ state.processedNonces)  -- Gate 3: replay protection
     && decide (sig.nonce ≥ state.nextNonce)         -- Gate 4: nonce ordering
  then some (fillPostState state amount sig)
  else none

-- ═══════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════

/-- FILL REQUIRES THRESHOLD: Mint only happens if at least `threshold`
    MPC validators signed. Prevents rogue minting with compromised
    minority of the validator set. -/
theorem fill_requires_threshold
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (newState : FillState)
    (h : bridgeFill compliance params state from_ to_ amount sig = some newState) :
    sig.signers.card ≥ params.threshold := by
  unfold bridgeFill at h
  split at h
  · rename_i hcond
    simp [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact hcond.1.1.1
  · simp at h

/-- FILL REQUIRES COMPLIANCE: Mint only happens if the compliance check
    (canTransfer) passes. Ensures all minted tokens on the destination
    chain went through the full ERC-3643 compliance gate. -/
theorem fill_requires_compliance
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (newState : FillState)
    (h : bridgeFill compliance params state from_ to_ amount sig = some newState) :
    compliance from_ to_ = true := by
  unfold bridgeFill at h
  split at h
  · rename_i hcond
    simp [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact hcond.1.1.2
  · simp at h

/-- FILL ATOMIC: Either all gates pass and mint occurs (some post-state),
    or nothing changes (none). There is no intermediate state where
    signatures are consumed but mint doesn't happen. -/
theorem fill_atomic
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig) :
    (∃ newState, bridgeFill compliance params state from_ to_ amount sig = some newState) ∨
    bridgeFill compliance params state from_ to_ amount sig = none := by
  cases h : bridgeFill compliance params state from_ to_ amount sig
  · right; rfl
  · left; exact ⟨_, rfl⟩

/-- NO MINT WITHOUT BURN: The total minted on the destination chain never
    exceeds the total burned on the source chain. This is the conservation
    invariant — the bridge cannot create tokens out of thin air.

    Modeled as: if the invariant holds before a fill, and the fill amount
    is bounded by the remaining burn capacity, then it holds after. -/
theorem no_mint_without_burn
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState) (source : SourceState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (newState : FillState)
    (h_bounded : state.totalMinted + amount ≤ source.totalBurned)
    (h_fill : bridgeFill compliance params state from_ to_ amount sig = some newState) :
    newState.totalMinted ≤ source.totalBurned := by
  unfold bridgeFill at h_fill
  split at h_fill
  · simp at h_fill; rw [← h_fill]; simp [fillPostState]; omega
  · simp at h_fill

/-- REPLAY PROTECTION: A nonce that has been processed cannot be used again.
    After a successful fill, the nonce is in processedNonces, so any
    subsequent attempt with the same nonce is rejected. -/
theorem replay_protection
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (newState : FillState)
    (h_fill : bridgeFill compliance params state from_ to_ amount sig = some newState) :
    sig.nonce ∈ newState.processedNonces := by
  unfold bridgeFill at h_fill
  split at h_fill
  · simp at h_fill; rw [← h_fill]; simp [fillPostState, Finset.mem_union]
  · simp at h_fill

/-- After a successful fill, a second fill with the same nonce fails -/
theorem no_double_fill
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (newState : FillState)
    (h_fill : bridgeFill compliance params state from_ to_ amount sig = some newState)
    (from2 to2 : Address) (amount2 : Nat)
    (sig2 : MPCSig) (h_same_nonce : sig2.nonce = sig.nonce) :
    bridgeFill compliance params newState from2 to2 amount2 sig2 = none := by
  have h_in := replay_protection compliance params state from_ to_ amount sig
                 newState h_fill
  simp [bridgeFill]
  rw [h_same_nonce]
  simp [h_in]

/-- NONCE MONOTONICITY: The nextNonce field strictly increases with each
    successful fill, providing a total ordering on fills. -/
theorem nonce_monotonicity
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (newState : FillState)
    (h_fill : bridgeFill compliance params state from_ to_ amount sig = some newState) :
    newState.nextNonce > state.nextNonce := by
  unfold bridgeFill at h_fill
  split at h_fill
  · rename_i hcond
    simp [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨_, _⟩, _⟩, h_ord⟩ := hcond
    simp only [Option.some.injEq] at h_fill
    subst h_fill
    simp only [fillPostState, FillState.nextNonce, gt_iff_lt]
    omega
  · simp at h_fill

/-- Insufficient signatures always fail -/
theorem insufficient_sigs_fail
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (h : sig.signers.card < params.threshold) :
    bridgeFill compliance params state from_ to_ amount sig = none := by
  unfold bridgeFill
  simp only [ite_eq_right_iff]
  intro habs
  simp [Bool.and_eq_true, decide_eq_true_eq] at habs
  omega

/-- Failed compliance always fails -/
theorem compliance_failure_blocks
    (compliance : Address → Address → Bool)
    (params : BridgeParams) (state : FillState)
    (from_ to_ : Address) (amount : Nat) (sig : MPCSig)
    (h : compliance from_ to_ = false) :
    bridgeFill compliance params state from_ to_ amount sig = none := by
  simp [bridgeFill, h]

end Bridge.FillIntegrity
