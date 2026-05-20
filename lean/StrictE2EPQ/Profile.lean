/-
  LUX_STRICT_E2E_PQ Profile Definition

  Models ChainSecurityProfile from
  luxfi/consensus/config/security_profile.go:244.

  The proposition `IsE2EPQ profile` is provable iff every Forbid* bit and
  every scheme field on `profile` matches strict-PQ values.

  Companion paper: ~/work/lux/papers/lp-stricte2epq/
  Companion TLA+: ~/work/lux/proofs/tla/StrictPQProfile.tla
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace StrictE2EPQ

/-! ## Scheme identifiers -/

/-- Signature scheme identifier (matches SigSchemeID in Go).
    The byte values follow the HIP-0077 §2 block layout:
    0x40+ = ML-DSA, 0x50+ = Pulsar-M, 0x80+ = SLH-DSA. -/
inductive SigSchemeID where
  | none      : SigSchemeID  -- zero-value-invalid
  | mldsa44   : SigSchemeID  -- 0x42 (devnet only)
  | mldsa65   : SigSchemeID  -- 0x40 (strict-PQ default)
  | mldsa87   : SigSchemeID  -- 0x41
  | pulsar44 : SigSchemeID  -- devnet only
  | pulsar65 : SigSchemeID  -- 0x50
  | pulsar87 : SigSchemeID  -- 0x51
  | slhdsa256s : SigSchemeID -- 0x80
  | ecdsaSecp256k1 : SigSchemeID  -- classical
  | ed25519        : SigSchemeID  -- classical
  | blsAggregate   : SigSchemeID  -- classical
  deriving DecidableEq, Repr

/-- Hash suite identifier. -/
inductive HashSuiteID where
  | none           : HashSuiteID  -- zero-value-invalid
  | sha3_384       : HashSuiteID  -- strict-PQ default
  | sha2_256       : HashSuiteID  -- classical
  | keccak256      : HashSuiteID  -- classical Ethereum
  deriving DecidableEq, Repr

/-- Proof policy identifier. -/
inductive ProofPolicyID where
  | none              : ProofPolicyID  -- zero-value-invalid
  | classical80       : ProofPolicyID  -- 80-bit classical
  | classical128      : ProofPolicyID  -- 128-bit classical
  | pq128             : ProofPolicyID  -- 128-bit PQ (strict-PQ)
  | pq256             : ProofPolicyID  -- 256-bit PQ
  deriving DecidableEq, Repr

/-- Proof backend identifier. -/
inductive ProofBackendID where
  | none           : ProofBackendID
  | p3q            : ProofBackendID  -- strict-PQ admitted
  | plonky3Sha3    : ProofBackendID  -- strict-PQ admitted
  | plonky3Poseidon : ProofBackendID -- forbidden (Poseidon not FIPS 202)
  | groth16        : ProofBackendID  -- forbidden (pairings + SRS)
  | halo2          : ProofBackendID
  deriving DecidableEq, Repr

/-- Wallet scheme identifier (transaction signing). -/
inductive WalletSchemeID where
  | none           : WalletSchemeID
  | mldsa65        : WalletSchemeID
  | mldsa87        : WalletSchemeID
  | ecdsa          : WalletSchemeID
  deriving DecidableEq, Repr

/-- Contract auth scheme identifier (permits). -/
inductive ContractAuthID where
  | none           : ContractAuthID
  | mldsa65        : ContractAuthID
  | mldsa87        : ContractAuthID
  | ecdsa712       : ContractAuthID  -- EIP-2612 / EIP-712 (classical)
  deriving DecidableEq, Repr

/-- Bridge profile identifier. -/
inductive BridgeProfileID where
  | none           : BridgeProfileID
  | strictPQ       : BridgeProfileID
  | fips           : BridgeProfileID
  | permissive     : BridgeProfileID
  deriving DecidableEq, Repr

/-- DRBG scheme identifier. -/
inductive DRBGSchemeID where
  | none           : DRBGSchemeID
  | hashDRBGSha3   : DRBGSchemeID  -- SP 800-90A Hash_DRBG-SHA3-384
  | hmacDRBG       : DRBGSchemeID  -- SP 800-90A HMAC_DRBG
  | ctrDRBG        : DRBGSchemeID  -- SP 800-90A CTR_DRBG
  deriving DecidableEq, Repr

/-! ## ChainSecurityProfile -/

/-- ChainSecurityProfile mirrors the Go struct at
    `luxfi/consensus/config/security_profile.go:244`.
    Aggregator lists (AllowedProofBackends, AllowedProofFormats) are
    modelled as `List ProofBackendID` to keep the proof tractable. -/
structure ChainSecurityProfile where
  profileID            : Nat
  profileName          : String
  -- profileHash is computed; not a constructor input
  hashSuiteID          : HashSuiteID
  identitySchemeID     : SigSchemeID
  finalitySchemeID     : SigSchemeID
  highValueSchemeID    : SigSchemeID
  proofPolicyID        : ProofPolicyID
  allowedProofBackends : List ProofBackendID
  minSoundnessBits     : Nat
  minHashOutputBits    : Nat
  requireTransparent   : Bool
  forbidPairings       : Bool
  forbidKZG            : Bool
  forbidTrustedSetup   : Bool
  forbidClassicalSNARKs : Bool
  forbidDevProofs      : Bool
  forbidFallbacks      : Bool
  requireTypedTxAuth   : Bool
  walletSchemeID       : WalletSchemeID
  contractAuthSchemeID : ContractAuthID
  bridgeProfileID      : BridgeProfileID
  drbgSchemeID         : DRBGSchemeID
  deriving Repr

/-! ## Strict-PQ classification -/

/-- A signature scheme is PQ-safe iff it is in the M-LWE / lattice
    family (ML-DSA, Pulsar-M) or the FIPS 205 SLH-DSA family. -/
def isPQScheme : SigSchemeID → Bool
  | .mldsa44      => true
  | .mldsa65      => true
  | .mldsa87      => true
  | .pulsar44    => true
  | .pulsar65    => true
  | .pulsar87    => true
  | .slhdsa256s   => true
  | _             => false

/-- A proof backend is strict-PQ-admissible iff it is in the
    `AllowedProofBackends` set. -/
def isStrictPQBackend : ProofBackendID → Bool
  | .p3q         => true
  | .plonky3Sha3 => true
  | _            => false

/-- A hash suite is strict-PQ-admissible iff it is FIPS 202. -/
def isStrictPQSuite : HashSuiteID → Bool
  | .sha3_384 => true
  | _         => false

/-- A wallet scheme is strict-PQ iff it is ML-DSA-65 or ML-DSA-87. -/
def isStrictPQWallet : WalletSchemeID → Bool
  | .mldsa65 => true
  | .mldsa87 => true
  | _        => false

/-- A contract auth scheme is strict-PQ iff it is ML-DSA-65 or -87. -/
def isStrictPQContractAuth : ContractAuthID → Bool
  | .mldsa65 => true
  | .mldsa87 => true
  | _        => false

/-- A bridge profile is strict-PQ iff it is `strictPQ` or `fips`. -/
def isStrictPQBridge : BridgeProfileID → Bool
  | .strictPQ => true
  | .fips     => true
  | _         => false

/-- A DRBG scheme is strict-PQ iff it is `hashDRBGSha3`. -/
def isStrictPQDRBG : DRBGSchemeID → Bool
  | .hashDRBGSha3 => true
  | _             => false

/-! ## The IsE2EPQ proposition -/

/-- `IsE2EPQ profile` is provable iff every enum field and every flag
    on `profile` matches strict-PQ values. This is the Lean 4
    counterpart to Definition~\ref{def:strict-pq} in the soundness
    paper. -/
def IsE2EPQ (p : ChainSecurityProfile) : Prop :=
  isStrictPQSuite p.hashSuiteID = true
  ∧ isPQScheme p.identitySchemeID = true
  ∧ isPQScheme p.finalitySchemeID = true
  ∧ isPQScheme p.highValueSchemeID = true
  ∧ p.proofPolicyID = .pq128
  ∧ (∀ b ∈ p.allowedProofBackends, isStrictPQBackend b = true)
  ∧ p.minSoundnessBits ≥ 128
  ∧ p.minHashOutputBits ≥ 384
  ∧ p.requireTransparent = true
  ∧ p.forbidPairings = true
  ∧ p.forbidKZG = true
  ∧ p.forbidTrustedSetup = true
  ∧ p.forbidClassicalSNARKs = true
  ∧ p.forbidDevProofs = true
  ∧ p.forbidFallbacks = true
  ∧ p.requireTypedTxAuth = true
  ∧ isStrictPQWallet p.walletSchemeID = true
  ∧ isStrictPQContractAuth p.contractAuthSchemeID = true
  ∧ isStrictPQBridge p.bridgeProfileID = true
  ∧ isStrictPQDRBG p.drbgSchemeID = true

/-! ## Production strict-PQ instance -/

/-- The production strict-PQ profile (matches
    `ProfileLuxStrictPQ` at `luxfi/consensus@12097034`). -/
def luxStrictPQ : ChainSecurityProfile := {
  profileID := 1
  profileName := "lux-strict-pq-v1"
  hashSuiteID := .sha3_384
  identitySchemeID := .mldsa65
  finalitySchemeID := .pulsar65
  highValueSchemeID := .pulsar87
  proofPolicyID := .pq128
  allowedProofBackends := [.p3q, .plonky3Sha3]
  minSoundnessBits := 128
  minHashOutputBits := 384
  requireTransparent := true
  forbidPairings := true
  forbidKZG := true
  forbidTrustedSetup := true
  forbidClassicalSNARKs := true
  forbidDevProofs := true
  forbidFallbacks := true
  requireTypedTxAuth := true
  walletSchemeID := .mldsa65
  contractAuthSchemeID := .mldsa65
  bridgeProfileID := .strictPQ
  drbgSchemeID := .hashDRBGSha3
}

/-- The production strict-PQ profile satisfies IsE2EPQ. -/
theorem luxStrictPQ_isE2EPQ : IsE2EPQ luxStrictPQ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl                        -- hashSuiteID = sha3_384
  · rfl                        -- identitySchemeID = mldsa65
  · rfl                        -- finalitySchemeID = pulsar65
  · rfl                        -- highValueSchemeID = pulsar87
  · rfl                        -- proofPolicyID = pq128
  · intro b hb                 -- allowedProofBackends
    simp [luxStrictPQ] at hb
    rcases hb with h | h
    · subst h; rfl
    · subst h; rfl
  · decide                     -- minSoundnessBits = 128 ≥ 128
  · decide                     -- minHashOutputBits = 384 ≥ 384
  · rfl                        -- requireTransparent = true
  · rfl                        -- forbidPairings = true
  · rfl                        -- forbidKZG = true
  · rfl                        -- forbidTrustedSetup = true
  · rfl                        -- forbidClassicalSNARKs = true
  · rfl                        -- forbidDevProofs = true
  · rfl                        -- forbidFallbacks = true
  · rfl                        -- requireTypedTxAuth = true
  · rfl                        -- walletSchemeID = mldsa65
  · rfl                        -- contractAuthSchemeID = mldsa65
  · rfl                        -- bridgeProfileID = strictPQ
  · rfl                        -- drbgSchemeID = hashDRBGSha3

/-! ## A permissive profile fails IsE2EPQ -/

/-- A permissive profile mixes classical and PQ; it does NOT satisfy
    IsE2EPQ. We construct one and show the proposition fails. -/
def luxPermissive : ChainSecurityProfile := {
  profileID := 2
  profileName := "lux-permissive"
  hashSuiteID := .sha3_384
  identitySchemeID := .ecdsaSecp256k1   -- classical
  finalitySchemeID := .pulsar65
  highValueSchemeID := .pulsar65
  proofPolicyID := .pq128
  allowedProofBackends := [.p3q]
  minSoundnessBits := 128
  minHashOutputBits := 384
  requireTransparent := true
  forbidPairings := false               -- relaxed!
  forbidKZG := true
  forbidTrustedSetup := true
  forbidClassicalSNARKs := true
  forbidDevProofs := true
  forbidFallbacks := false              -- relaxed!
  requireTypedTxAuth := false           -- relaxed!
  walletSchemeID := .ecdsa              -- classical
  contractAuthSchemeID := .ecdsa712
  bridgeProfileID := .permissive
  drbgSchemeID := .ctrDRBG
}

/-- The permissive profile does NOT satisfy IsE2EPQ. -/
theorem luxPermissive_not_isE2EPQ : ¬ IsE2EPQ luxPermissive := by
  unfold IsE2EPQ luxPermissive
  intro h
  -- The identity scheme is ECDSA, which is not PQ.
  exact absurd h.2.1 (by decide)

end StrictE2EPQ
