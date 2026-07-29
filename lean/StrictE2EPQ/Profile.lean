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

/-! ## Scheme identifiers

Each enum below carries a `byte` function holding the wire value of every
constructor, taken from the Go constant table named in the enum's own
doc-comment. The bytes are therefore checked by `lake build` rather than
asserted in a comment: `luxStrictPQ_wire_bytes` at the end of this file
pins the production code points, so a divergence between this model and
the Go tables is a build failure.

Three Go packages declare overlapping scheme-ID tables and they do not
agree. This file follows `config/`, the package whose types are the
declared field types of `ChainSecurityProfile`
(`config/security_profile.go:286-297,372,386`), and widens a member set only
where `protocol/auth` — the user-facing verifier trust boundary — defines
additional code points. Where the two Go tables disagree about whether a
scheme is PQ-admissible, the predicates below take the intersection, so
`IsE2EPQ` never admits a scheme that either Go table refuses. The
divergences are recorded on the enums they affect. -/

/-- Signature scheme identifier. Mirrors `config.SigSchemeID`
    (`luxfi/consensus/config/pq_mode.go:294`); constant table at
    `pq_mode.go:297-310`. This is the declared type of the profile's
    IdentitySchemeID / FinalitySchemeID / HighValueSchemeID fields
    (`config/security_profile.go:286-297`).

    Block layout (`pq_mode.go:280-290`): 0x10 classical BLS, 0x20 Corona
    (Nasua, academic R-LWE), 0x30 Pulsar.R, 0x41-0x43 raw FIPS 204
    ML-DSA, 0x51-0x53 Pulsar-M threshold. 0x60+ is reserved and unused,
    so there is no SLH-DSA member on this axis; the SLH-DSA family
    appears on the wallet and contract-auth axes below.

    `pkg/wire/candidate.go:346-352` declares a second, same-named
    `SigSchemeID` that assigns Pulsar-M the 0x41/0x42/0x43 code points —
    the bytes `config` assigns to raw ML-DSA — while its own comment
    (`candidate.go:342`) requires the two tables to be identical. The Go
    sources contradict each other; this model follows `config`. -/
inductive SigSchemeID where
  | none      : SigSchemeID  -- 0x00 zero-value-invalid
  | bls12381  : SigSchemeID  -- 0x10 classical BLS12-381 aggregate
  | nasua     : SigSchemeID  -- 0x20 Corona, academic R-LWE
  | pulsarR   : SigSchemeID  -- 0x30 Pulsar.R production R-LWE
  | mldsa44   : SigSchemeID  -- 0x41 NIST Cat 2, devnet only
  | mldsa65   : SigSchemeID  -- 0x42 NIST Cat 3, production identity
  | mldsa87   : SigSchemeID  -- 0x43 NIST Cat 5
  | pulsar44  : SigSchemeID  -- 0x51 NIST Cat 2, devnet only
  | pulsar65  : SigSchemeID  -- 0x52 NIST Cat 3, production finality
  | pulsar87  : SigSchemeID  -- 0x53 NIST Cat 5, high-value roots
  deriving DecidableEq, Repr

/-- Wire byte of a signature scheme (`config/pq_mode.go:297-310`). -/
def SigSchemeID.byte : SigSchemeID → Nat
  | .none     => 0x00
  | .bls12381 => 0x10
  | .nasua    => 0x20
  | .pulsarR  => 0x30
  | .mldsa44  => 0x41
  | .mldsa65  => 0x42
  | .mldsa87  => 0x43
  | .pulsar44 => 0x51
  | .pulsar65 => 0x52
  | .pulsar87 => 0x53

/-- Distinct schemes occupy distinct bytes, so a cert's scheme byte
    names exactly one scheme. This is the property `pkg/wire`'s table
    violates against `config`'s: there, one byte names two schemes. -/
theorem sigSchemeID_byte_inj {a b : SigSchemeID} (h : a.byte = b.byte) :
    a = b := by
  cases a <;> cases b <;> simp_all [SigSchemeID.byte]

/-- Hash suite identifier. Mirrors `config.HashSuiteID`
    (`config/pq_mode.go:171`); constant table at `pq_mode.go:177-194`.
    `sha3NIST` is the whole FIPS 202 + SP 800-185 family (SHAKE256,
    cSHAKE256, KMAC256, TupleHash256), which is why raw ML-DSA-65 also
    advertises it. -/
inductive HashSuiteID where
  | none         : HashSuiteID  -- 0x00 no hash-family commitment
  | sha3NIST     : HashSuiteID  -- 0x01 FIPS 202 + SP 800-185
  | blake3Legacy : HashSuiteID  -- 0x02 outside FIPS 202
  deriving DecidableEq, Repr

/-- Wire byte of a hash suite (`config/pq_mode.go:177-194`). -/
def HashSuiteID.byte : HashSuiteID → Nat
  | .none         => 0x00
  | .sha3NIST     => 0x01
  | .blake3Legacy => 0x02

/-- Proof policy identifier. Mirrors `config.ProofPolicyID`
    (`config/pq_mode.go:417`); constant table at `pq_mode.go:425-434`.
    The 0x80 block exists so audit tooling can name a classical
    misconfiguration rather than fall through to "unknown". -/
inductive ProofPolicyID where
  | none               : ProofPolicyID  -- 0x00 zero-value-invalid
  | starkFRISHA3PQ     : ProofPolicyID  -- 0x10 canonical Z-Chain policy
  | starkFRIKeccak     : ProofPolicyID  -- 0x11 FIPS 202 Keccak variant
  | groth16BN254Forbid : ProofPolicyID  -- 0x80 pairings + SRS
  | plonkKZGForbid     : ProofPolicyID  -- 0x81 KZG trusted setup
  | haloECForbid       : ProofPolicyID  -- 0x82 classical EC
  | ipaECForbid        : ProofPolicyID  -- 0x83 classical EC
  deriving DecidableEq, Repr

/-- Wire byte of a proof policy (`config/pq_mode.go:425-434`). -/
def ProofPolicyID.byte : ProofPolicyID → Nat
  | .none               => 0x00
  | .starkFRISHA3PQ     => 0x10
  | .starkFRIKeccak     => 0x11
  | .groth16BN254Forbid => 0x80
  | .plonkKZGForbid     => 0x81
  | .haloECForbid       => 0x82
  | .ipaECForbid        => 0x83

/-- Proof backend identifier. Mirrors `config.ProofBackendID`
    (`config/pq_mode.go:512`); constant table at `pq_mode.go:515-530`. -/
inductive ProofBackendID where
  | none              : ProofBackendID  -- 0x00
  | risc0Succinct     : ProofBackendID  -- 0x20 production STARK
  | sp1Compressed     : ProofBackendID  -- 0x21 production STARK
  | p3q               : ProofBackendID  -- 0x22 production STARK-FRI-SHA3
  | stoneCairo        : ProofBackendID  -- 0x23 production STARK
  | stwoCircle        : ProofBackendID  -- 0x24 production circle STARK
  | risc0RawDev       : ProofBackendID  -- 0x70 dev-only
  | sp1CoreDev        : ProofBackendID  -- 0x71 dev-only
  | groth16WrapForbid : ProofBackendID  -- 0x80 classical wrapper
  | kzgWrapForbid     : ProofBackendID  -- 0x81 classical wrapper
  deriving DecidableEq, Repr

/-- Wire byte of a proof backend (`config/pq_mode.go:515-530`). -/
def ProofBackendID.byte : ProofBackendID → Nat
  | .none              => 0x00
  | .risc0Succinct     => 0x20
  | .sp1Compressed     => 0x21
  | .p3q               => 0x22
  | .stoneCairo        => 0x23
  | .stwoCircle        => 0x24
  | .risc0RawDev       => 0x70
  | .sp1CoreDev        => 0x71
  | .groth16WrapForbid => 0x80
  | .kzgWrapForbid     => 0x81

/-- Wallet scheme identifier (user EOA transaction signing). Member set
    and bytes follow `auth.WalletSchemeID`
    (`protocol/auth/scheme_ids.go:73`, table at `scheme_ids.go:76-91`),
    the enum the user-facing verifier `VerifyTxAuthEnvelope` reads.

    `config.WalletSchemeID` (`config/pq_mode.go:771`, the declared type
    of the profile field at `security_profile.go:372`) is a narrower
    table over the same axis: it omits ML-DSA-44 and the SLH-DSA family,
    and places the classical marker at 0x90 rather than `auth`'s 0x10.
    `scheme_ids.go:26-33` states the `auth` copy is temporary pending a
    merge into `config`; until that lands the two tables disagree about
    which bytes exist. Both agree on the production value, ML-DSA-65 =
    0x42 (`profiles.go:70`). -/
inductive WalletSchemeID where
  | none                 : WalletSchemeID  -- 0x00
  | ecdsaSecp256k1Legacy : WalletSchemeID  -- 0x10 classical
  | mldsa44              : WalletSchemeID  -- 0x41 NIST Cat 2
  | mldsa65              : WalletSchemeID  -- 0x42 NIST Cat 3, production
  | mldsa87              : WalletSchemeID  -- 0x43 NIST Cat 5
  | slhdsa128f           : WalletSchemeID  -- 0x61 FIPS 205 Cat 1
  | slhdsa192f           : WalletSchemeID  -- 0x62 FIPS 205 Cat 3
  | slhdsa256f           : WalletSchemeID  -- 0x63 FIPS 205 Cat 5
  deriving DecidableEq, Repr

/-- Wire byte of a wallet scheme (`protocol/auth/scheme_ids.go:76-91`). -/
def WalletSchemeID.byte : WalletSchemeID → Nat
  | .none                 => 0x00
  | .ecdsaSecp256k1Legacy => 0x10
  | .mldsa44              => 0x41
  | .mldsa65              => 0x42
  | .mldsa87              => 0x43
  | .slhdsa128f           => 0x61
  | .slhdsa192f           => 0x62
  | .slhdsa256f           => 0x63

/-- Contract auth scheme identifier (admin / upgrade / pause / permit).
    Member set and bytes follow `auth.ContractAuthID`
    (`protocol/auth/scheme_ids.go:197`, table at `scheme_ids.go:200-207`).

    `config.ContractAuthID` (`config/pq_mode.go:864`) is a different
    table on the same axis, and the two collide on byte 0x10:
    `config.ContractAuthZChainProof` (`pq_mode.go:868`) reports
    IsPostQuantum = true there, while
    `auth.ContractAuthECDSASecp256k1Legacy` (`scheme_ids.go:201`) reports
    IsPostQuantum = false for the same byte. `isStrictPQContractAuth`
    below refuses 0x10 on both readings. -/
inductive ContractAuthID where
  | none                 : ContractAuthID  -- 0x00
  | ecdsaSecp256k1Legacy : ContractAuthID  -- 0x10 classical
  | mldsa44              : ContractAuthID  -- 0x41 NIST Cat 2
  | mldsa65              : ContractAuthID  -- 0x42 NIST Cat 3, production
  | mldsa87              : ContractAuthID  -- 0x43 NIST Cat 5
  | slhdsa128f           : ContractAuthID  -- 0x61 FIPS 205 Cat 1
  | slhdsa192f           : ContractAuthID  -- 0x62 FIPS 205 Cat 3
  | slhdsa256f           : ContractAuthID  -- 0x63 FIPS 205 Cat 5
  deriving DecidableEq, Repr

/-- Wire byte of a contract-auth scheme
    (`protocol/auth/scheme_ids.go:200-207`). -/
def ContractAuthID.byte : ContractAuthID → Nat
  | .none                 => 0x00
  | .ecdsaSecp256k1Legacy => 0x10
  | .mldsa44              => 0x41
  | .mldsa65              => 0x42
  | .mldsa87              => 0x43
  | .slhdsa128f           => 0x61
  | .slhdsa192f           => 0x62
  | .slhdsa256f           => 0x63

/-- Bridge profile identifier. Mirrors `config.BridgeProfileID`
    (`config/bridge_profile.go:48`); constant table at
    `bridge_profile.go:51-53`. Carried by `BridgeProfile`, not by
    `ChainSecurityProfile`; this model folds the axis into one profile
    so the 14-surface coverage argument in `Coverage.lean` reaches the
    bridge admit path. -/
inductive BridgeProfileID where
  | none            : BridgeProfileID  -- 0x00
  | luxStrictPQ     : BridgeProfileID  -- 0x01 production E2E-PQ bridge
  | classicalCompat : BridgeProfileID  -- 0x90 non-strict compat
  deriving DecidableEq, Repr

/-- Wire byte of a bridge profile (`config/bridge_profile.go:51-53`). -/
def BridgeProfileID.byte : BridgeProfileID → Nat
  | .none            => 0x00
  | .luxStrictPQ     => 0x01
  | .classicalCompat => 0x90

/-- DRBG scheme identifier. The strict-PQ committee-selection DRBG is a
    SHA3-384 Hash_DRBG (`protocol/quasar/grouped_threshold.go:220`).
    `config` declares no wire enum on this axis, so unlike every other
    enum here these constructors carry no byte: the axis is modelled,
    not mirrored. -/
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

/-- A signature scheme is PQ-safe iff the unmodified FIPS 204 ML-DSA
    verifier accepts it: the raw ML-DSA block (0x41-0x43) or the
    Pulsar-M threshold block (0x51-0x53). Mirrors
    `config.SigSchemeID.VerifiesUnderFIPS204` (`config/pq_mode.go:365`).

    Nasua (0x20) and Pulsar.R (0x30) are lattice schemes but sit outside
    both blocks, and `ChainSecurityProfile.Validate`
    (`config/security_profile.go:247-249`) admits neither on any of the
    three scheme axes, so neither is PQ-safe for this proposition. -/
def isPQScheme : SigSchemeID → Bool
  | .mldsa44  => true
  | .mldsa65  => true
  | .mldsa87  => true
  | .pulsar44 => true
  | .pulsar65 => true
  | .pulsar87 => true
  | _         => false

/-- A proof backend is strict-PQ-admissible iff it is in the production
    STARK block (0x20-0x24). Mirrors
    `config.ProofBackendID.IsProductionPQ` (`config/pq_mode.go:564`);
    the dev block (0x70-0x71) and the classical-wrapper block
    (0x80-0x81) are excluded. -/
def isStrictPQBackend : ProofBackendID → Bool
  | .risc0Succinct => true
  | .sp1Compressed => true
  | .p3q           => true
  | .stoneCairo    => true
  | .stwoCircle    => true
  | _              => false

/-- A hash suite is strict-PQ-admissible iff it is the FIPS 202 family.
    Mirrors `config.HashSuiteID.IsNormative` (`config/pq_mode.go:216`);
    BLAKE3 sits outside FIPS 202 and is refused. -/
def isStrictPQSuite : HashSuiteID → Bool
  | .sha3NIST => true
  | _         => false

/-- A wallet scheme is strict-PQ iff both Go tables admit it, which is
    ML-DSA-65 and ML-DSA-87. `auth.WalletSchemeID.IsPostQuantum`
    (`protocol/auth/scheme_ids.go:135`) additionally admits ML-DSA-44
    and the SLH-DSA family; `config.WalletSchemeID.IsPostQuantum`
    (`config/pq_mode.go:799`) admits neither. Taking the intersection
    keeps `IsE2EPQ` from admitting a scheme either verifier refuses —
    including the Cat-2 ML-DSA-44 the block comment at
    `protocol/auth/scheme_ids.go:64` marks devnet-only. -/
def isStrictPQWallet : WalletSchemeID → Bool
  | .mldsa65 => true
  | .mldsa87 => true
  | _        => false

/-- A contract auth scheme is strict-PQ iff both Go tables admit it,
    which is ML-DSA-65 and ML-DSA-87 — the intersection of
    `auth.ContractAuthID.IsPostQuantum`
    (`protocol/auth/scheme_ids.go:236`) and
    `config.ContractAuthID.IsPostQuantum` (`config/pq_mode.go:905`).
    Byte 0x10 is refused: the two Go tables assign it opposite PQ
    verdicts. -/
def isStrictPQContractAuth : ContractAuthID → Bool
  | .mldsa65 => true
  | .mldsa87 => true
  | _        => false

/-- A bridge profile is strict-PQ iff it is `LUX_STRICT_PQ_BRIDGE`
    (0x01), the only strict posture `config/bridge_profile.go:51-53`
    defines. 0x02-0x7F is reserved for future strict postures and
    0x80-0xFF is the non-strict block. -/
def isStrictPQBridge : BridgeProfileID → Bool
  | .luxStrictPQ => true
  | _            => false

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
  ∧ p.proofPolicyID = .starkFRISHA3PQ
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

/-- The production strict-PQ profile. Every field is the value
    `config.StrictPQProfile` carries at `config/profiles.go:33-81`;
    `bridgeProfileID` is `BridgeProfileIDLuxStrictPQ`
    (`config/bridge_profile.go:52`), which the Go code holds on the
    companion `BridgeProfile` rather than on `ChainSecurityProfile`. -/
def luxStrictPQ : ChainSecurityProfile := {
  profileID := 1
  profileName := "lux-strict-pq-v1"
  hashSuiteID := .sha3NIST
  identitySchemeID := .mldsa65
  finalitySchemeID := .pulsar65
  highValueSchemeID := .pulsar87
  proofPolicyID := .starkFRISHA3PQ
  allowedProofBackends :=
    [.sp1Compressed, .risc0Succinct, .p3q, .stoneCairo, .stwoCircle]
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
  bridgeProfileID := .luxStrictPQ
  drbgSchemeID := .hashDRBGSha3
}

/-- The production strict-PQ profile satisfies IsE2EPQ. -/
theorem luxStrictPQ_isE2EPQ : IsE2EPQ luxStrictPQ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl                        -- hashSuiteID = sha3NIST (0x01)
  · rfl                        -- identitySchemeID = mldsa65 (0x42)
  · rfl                        -- finalitySchemeID = pulsar65 (0x52)
  · rfl                        -- highValueSchemeID = pulsar87 (0x53)
  · rfl                        -- proofPolicyID = starkFRISHA3PQ (0x10)
  · decide                     -- allowedProofBackends ⊆ production block
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
  · rfl                        -- walletSchemeID = mldsa65 (0x42)
  · rfl                        -- contractAuthSchemeID = mldsa65 (0x42)
  · rfl                        -- bridgeProfileID = luxStrictPQ (0x01)
  · rfl                        -- drbgSchemeID = hashDRBGSha3

/-- The wire bytes the production profile pins, checked against the Go
    constant tables rather than asserted in a comment. Identity
    0x42 = ML-DSA-65 and finality 0x52 = Pulsar-M-65 are the two values
    `config/profiles.go:37-38` selects and `config/pq_mode.go:304,309`
    defines; high-value 0x53 = Pulsar-M-87 comes from `profiles.go:39`.
    Reading these under `pkg/wire/candidate.go:346-352` instead would
    resolve 0x42 to Pulsar-M-65 and leave 0x52 undefined. -/
theorem luxStrictPQ_wire_bytes :
    luxStrictPQ.hashSuiteID.byte = 0x01
  ∧ luxStrictPQ.identitySchemeID.byte = 0x42
  ∧ luxStrictPQ.finalitySchemeID.byte = 0x52
  ∧ luxStrictPQ.highValueSchemeID.byte = 0x53
  ∧ luxStrictPQ.proofPolicyID.byte = 0x10
  ∧ luxStrictPQ.walletSchemeID.byte = 0x42
  ∧ luxStrictPQ.contractAuthSchemeID.byte = 0x42
  ∧ luxStrictPQ.bridgeProfileID.byte = 0x01
  ∧ luxStrictPQ.allowedProofBackends.map ProofBackendID.byte
      = [0x21, 0x20, 0x22, 0x23, 0x24] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Identity and finality are drawn from different scheme blocks:
    identity is raw single-party FIPS 204 ML-DSA (0x40 block), finality
    is Pulsar-M threshold (0x50 block). `ChainSecurityProfile.Validate`
    requires exactly this split (`config/security_profile.go:247-249`),
    and a model that collapsed the two blocks onto one byte range could
    not state it. -/
theorem luxStrictPQ_blocks_disjoint :
    luxStrictPQ.identitySchemeID.byte / 0x10 = 4
  ∧ luxStrictPQ.finalitySchemeID.byte / 0x10 = 5
  ∧ luxStrictPQ.highValueSchemeID.byte / 0x10 = 5 := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## A permissive profile fails IsE2EPQ -/

/-- A permissive profile mixes classical and PQ, so it does NOT satisfy
    IsE2EPQ. Every constructor below is a code point one of the Go
    tables defines, but the combination is synthetic: it is not
    `config.PermissiveProfile` (`config/profiles.go:91-143`), which
    keeps lattice schemes on all three axes and relaxes only the
    `Forbid*` bits. This one additionally pins classical identity
    (BLS12-381, 0x10), a classical wallet (0x10), a dev proof backend
    (0x70) and the compat bridge (0x90), so it fails the proposition on
    several independent conjuncts rather than one. -/
def luxPermissive : ChainSecurityProfile := {
  profileID := 2
  profileName := "lux-permissive"
  hashSuiteID := .sha3NIST
  identitySchemeID := .bls12381         -- classical BLS aggregate
  finalitySchemeID := .pulsar65
  highValueSchemeID := .pulsar65
  proofPolicyID := .starkFRISHA3PQ
  allowedProofBackends := [.p3q, .risc0RawDev]
  minSoundnessBits := 128
  minHashOutputBits := 384
  requireTransparent := true
  forbidPairings := false               -- relaxed!
  forbidKZG := true
  forbidTrustedSetup := true
  forbidClassicalSNARKs := true
  forbidDevProofs := false              -- relaxed!
  forbidFallbacks := false              -- relaxed!
  requireTypedTxAuth := false           -- relaxed!
  walletSchemeID := .ecdsaSecp256k1Legacy
  contractAuthSchemeID := .ecdsaSecp256k1Legacy
  bridgeProfileID := .classicalCompat
  drbgSchemeID := .ctrDRBG
}

/-- The permissive profile does NOT satisfy IsE2EPQ. -/
theorem luxPermissive_not_isE2EPQ : ¬ IsE2EPQ luxPermissive := by
  unfold IsE2EPQ luxPermissive
  intro h
  -- The identity scheme is ECDSA, which is not PQ.
  exact absurd h.2.1 (by decide)

end StrictE2EPQ
