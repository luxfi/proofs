/-
  LUX_STRICT_E2E_PQ Surface Coverage

  Theorem: under a strict-PQ profile, every one of the 14 enumerated
  surfaces is bound to a PQ primitive. This is the Lean 4 counterpart
  to Theorem E2E-PQ-COVERAGE in
  `~/work/lux/proofs/strict-e2e-pq/strict-e2e-pq-soundness.tex`.

  The proof is by structural decomposition of `IsE2EPQ`: each field
  fixes one surface; the conjunction of all fields fixes all surfaces.

  Companion paper: ~/work/lux/papers/lp-stricte2epq/sections/01-intro.tex
-/

import StrictE2EPQ.Profile
import Mathlib.Tactic

namespace StrictE2EPQ

/-! ## Field projections from IsE2EPQ -/

/-- Project the 20 conjuncts of IsE2EPQ into named lemmas so downstream
    proofs do not have to walk the conjunction tree by hand. Each lemma
    extracts one bound from the conjunction. -/

lemma isE2EPQ_suite {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isStrictPQSuite p.hashSuiteID = true := h.1

lemma isE2EPQ_identity {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isPQScheme p.identitySchemeID = true := h.2.1

lemma isE2EPQ_finality {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isPQScheme p.finalitySchemeID = true := h.2.2.1

lemma isE2EPQ_highValue {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isPQScheme p.highValueSchemeID = true := h.2.2.2.1

lemma isE2EPQ_proofPolicy {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.proofPolicyID = .pq128 := h.2.2.2.2.1

lemma isE2EPQ_backends {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    ∀ b ∈ p.allowedProofBackends, isStrictPQBackend b = true :=
  h.2.2.2.2.2.1

lemma isE2EPQ_soundnessBits {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.minSoundnessBits ≥ 128 := h.2.2.2.2.2.2.1

lemma isE2EPQ_hashOutputBits {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.minHashOutputBits ≥ 384 := h.2.2.2.2.2.2.2.1

lemma isE2EPQ_requireTransparent {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.requireTransparent = true := h.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_forbidPairings {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.forbidPairings = true := h.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_forbidKZG {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.forbidKZG = true := h.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_forbidTrustedSetup {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.forbidTrustedSetup = true := h.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_forbidClassicalSNARKs {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.forbidClassicalSNARKs = true := h.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_forbidDevProofs {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.forbidDevProofs = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_forbidFallbacks {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.forbidFallbacks = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_requireTypedTxAuth {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    p.requireTypedTxAuth = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_wallet {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isStrictPQWallet p.walletSchemeID = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_contractAuth {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isStrictPQContractAuth p.contractAuthSchemeID = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_bridge {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isStrictPQBridge p.bridgeProfileID = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma isE2EPQ_drbg {p : ChainSecurityProfile} (h : IsE2EPQ p) :
    isStrictPQDRBG p.drbgSchemeID = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## The 14 surfaces, named -/

/-- The 14 surfaces over which strict-PQ claims coverage. Each constructor
    names one surface; the proposition `SurfaceIsPQ` below states what
    PQ-coverage means for that surface. -/
inductive Surface where
  | profileBoot         : Surface  -- 1.  ChainSecurityProfile loaded
  | identityRegister    : Surface  -- 2.  OpRegisterKey
  | identityRotate      : Surface  -- 3.  OpRotateKey
  | identityRevoke      : Surface  -- 4.  OpRevokeKey
  | sessionAuth         : Surface  -- 5.  OpAuthorizeSession
  | txAuth              : Surface  -- 6.  TxAuthEnvelope
  | contractPermit      : Surface  -- 7.  PQPermit
  | zchainCommit        : Surface  -- 8.  ZRegistryRoots
  | execVerifyAuth      : Surface  -- 9.  VerifyAuthPassed
  | finalityBind        : Surface  -- 10. ComputeRoundDigest
  | finalitySign        : Surface  -- 11. Pulsar-M
  | proofVerify         : Surface  -- 12. p3q
  | p2pTransport        : Surface  -- 13. ML-KEM + ML-DSA
  | bridgeAdmit         : Surface  -- 14. BridgeProfile
  deriving DecidableEq, Repr

/-- `SurfaceIsPQ p s` is the proposition that surface `s` is bound to a
    PQ primitive under profile `p`. -/
def SurfaceIsPQ (p : ChainSecurityProfile) : Surface → Prop
  | .profileBoot      => isStrictPQSuite p.hashSuiteID = true
  | .identityRegister => isPQScheme p.identitySchemeID = true
  | .identityRotate   => isPQScheme p.identitySchemeID = true
  | .identityRevoke   => isPQScheme p.identitySchemeID = true
  | .sessionAuth      => isPQScheme p.identitySchemeID = true
  | .txAuth           => isStrictPQWallet p.walletSchemeID = true
                       ∧ p.requireTypedTxAuth = true
  | .contractPermit   => isStrictPQContractAuth p.contractAuthSchemeID = true
  | .zchainCommit     => isStrictPQSuite p.hashSuiteID = true
  | .execVerifyAuth   => isStrictPQSuite p.hashSuiteID = true
  | .finalityBind     => isStrictPQSuite p.hashSuiteID = true
  | .finalitySign     => isPQScheme p.finalitySchemeID = true
  | .proofVerify      => (∀ b ∈ p.allowedProofBackends, isStrictPQBackend b = true)
                       ∧ p.forbidPairings = true
                       ∧ p.forbidKZG = true
                       ∧ p.forbidTrustedSetup = true
                       ∧ p.forbidClassicalSNARKs = true
  | .p2pTransport     => isPQScheme p.identitySchemeID = true
                       ∧ isStrictPQSuite p.hashSuiteID = true
  | .bridgeAdmit      => isStrictPQBridge p.bridgeProfileID = true

/-! ## The 14-path coverage theorem -/

/-- For a strict-PQ profile, every surface is PQ-bound. This is
    Theorem E2E-PQ-COVERAGE from the soundness paper. -/
theorem coverage (p : ChainSecurityProfile) (hp : IsE2EPQ p) :
    ∀ s : Surface, SurfaceIsPQ p s := by
  intro s
  cases s
  case profileBoot      => exact isE2EPQ_suite hp
  case identityRegister => exact isE2EPQ_identity hp
  case identityRotate   => exact isE2EPQ_identity hp
  case identityRevoke   => exact isE2EPQ_identity hp
  case sessionAuth      => exact isE2EPQ_identity hp
  case txAuth           => exact ⟨isE2EPQ_wallet hp, isE2EPQ_requireTypedTxAuth hp⟩
  case contractPermit   => exact isE2EPQ_contractAuth hp
  case zchainCommit     => exact isE2EPQ_suite hp
  case execVerifyAuth   => exact isE2EPQ_suite hp
  case finalityBind     => exact isE2EPQ_suite hp
  case finalitySign     => exact isE2EPQ_finality hp
  case proofVerify      => exact ⟨isE2EPQ_backends hp,
                                   isE2EPQ_forbidPairings hp,
                                   isE2EPQ_forbidKZG hp,
                                   isE2EPQ_forbidTrustedSetup hp,
                                   isE2EPQ_forbidClassicalSNARKs hp⟩
  case p2pTransport     => exact ⟨isE2EPQ_identity hp, isE2EPQ_suite hp⟩
  case bridgeAdmit      => exact isE2EPQ_bridge hp

/-! ## Bridge invariant: PQ E2E implies no classical admin -/

/-- A bridge profile state pairs the two booleans that this paper's
    Section 11 constrains. -/
structure BridgeProfileState where
  allowsClassicalAdmin : Bool
  postQuantumEndToEnd  : Bool

/-- The bridge invariant: PQ-E2E excludes classical admin. -/
def BridgeInvariant (b : BridgeProfileState) : Prop :=
  b.postQuantumEndToEnd = true → b.allowsClassicalAdmin = false

/-- A bridge profile cannot simultaneously claim PostQuantumEndToEnd
    and AllowsClassicalAdmin. -/
theorem bridge_pq_no_classical (b : BridgeProfileState)
    (hp : b.postQuantumEndToEnd = true) (hc : b.allowsClassicalAdmin = true) :
    ¬ BridgeInvariant b := by
  intro h
  have := h hp
  rw [hc] at this
  exact Bool.noConfusion this

/-! ## Forbid* relaxation breaks IsE2EPQ -/

/-- Relaxing ForbidPairings to false breaks IsE2EPQ. -/
theorem relax_pairings_breaks (p : ChainSecurityProfile)
    (_hp : IsE2EPQ p)
    (q : ChainSecurityProfile)
    (h_eq : q = { p with forbidPairings := false }) :
    ¬ IsE2EPQ q := by
  intro hq
  have hqf : q.forbidPairings = true := isE2EPQ_forbidPairings hq
  rw [h_eq] at hqf
  exact Bool.noConfusion hqf

/-- Relaxing ForbidKZG to false breaks IsE2EPQ. -/
theorem relax_kzg_breaks (p : ChainSecurityProfile)
    (_hp : IsE2EPQ p)
    (q : ChainSecurityProfile)
    (h_eq : q = { p with forbidKZG := false }) :
    ¬ IsE2EPQ q := by
  intro hq
  have hqf : q.forbidKZG = true := isE2EPQ_forbidKZG hq
  rw [h_eq] at hqf
  exact Bool.noConfusion hqf

/-- Relaxing RequireTypedTxAuth to false breaks IsE2EPQ. -/
theorem relax_typed_tx_auth_breaks (p : ChainSecurityProfile)
    (_hp : IsE2EPQ p)
    (q : ChainSecurityProfile)
    (h_eq : q = { p with requireTypedTxAuth := false }) :
    ¬ IsE2EPQ q := by
  intro hq
  have hqf : q.requireTypedTxAuth = true := isE2EPQ_requireTypedTxAuth hq
  rw [h_eq] at hqf
  exact Bool.noConfusion hqf

/-- Relaxing ForbidTrustedSetup to false breaks IsE2EPQ. -/
theorem relax_trusted_setup_breaks (p : ChainSecurityProfile)
    (q : ChainSecurityProfile)
    (h_eq : q = { p with forbidTrustedSetup := false }) :
    ¬ IsE2EPQ q := by
  intro hq
  have hqf : q.forbidTrustedSetup = true := isE2EPQ_forbidTrustedSetup hq
  rw [h_eq] at hqf
  exact Bool.noConfusion hqf

/-- Relaxing ForbidFallbacks to false breaks IsE2EPQ. -/
theorem relax_fallbacks_breaks (p : ChainSecurityProfile)
    (q : ChainSecurityProfile)
    (h_eq : q = { p with forbidFallbacks := false }) :
    ¬ IsE2EPQ q := by
  intro hq
  have hqf : q.forbidFallbacks = true := isE2EPQ_forbidFallbacks hq
  rw [h_eq] at hqf
  exact Bool.noConfusion hqf

end StrictE2EPQ
