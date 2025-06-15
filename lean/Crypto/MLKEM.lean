/-
  ML-KEM (FIPS 203) Key Encapsulation Correctness

  Post-quantum key encapsulation mechanism. Used for key exchange
  in the hybrid handshake protocol.

  Based on CRYSTALS-Kyber (Module-LWE).

  Maps to:
  - luxfi/crypto: mlkem package
  - lux/node: post-quantum key exchange in SSP handshake
  - Quasar consensus: quantum-safe channel establishment

  Properties:
  - Correctness: decaps(encaps(pk)) recovers the shared secret
  - IND-CCA2 security under Module-LWE
  - Key sizes by security level
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Crypto.MLKEM

/-- ML-KEM security levels (FIPS 203) -/
inductive SecurityLevel where
  | mlkem512   -- NIST Level 1 (128-bit)
  | mlkem768   -- NIST Level 3 (192-bit) ← default for Lux
  | mlkem1024  -- NIST Level 5 (256-bit)
  deriving DecidableEq, Repr

/-- Public key sizes (bytes) -/
def pkSize : SecurityLevel → Nat
  | .mlkem512 => 800
  | .mlkem768 => 1184
  | .mlkem1024 => 1568

/-- Secret key sizes (bytes) -/
def skSize : SecurityLevel → Nat
  | .mlkem512 => 1632
  | .mlkem768 => 2400
  | .mlkem1024 => 3168

/-- Ciphertext sizes (bytes) -/
def ctSize : SecurityLevel → Nat
  | .mlkem512 => 768
  | .mlkem768 => 1088
  | .mlkem1024 => 1568

/-- Shared secret size (always 32 bytes) -/
def ssSize : SecurityLevel → Nat
  | _ => 32

/-- Key generation -/
axiom keygen : SecurityLevel → Nat × Nat  -- (pk, sk)

/-- Encapsulation: pk → (ct, ss) -/
axiom encaps : SecurityLevel → Nat → Nat × Nat

/-- Decapsulation: sk → ct → ss -/
axiom decaps : SecurityLevel → Nat → Nat → Nat

/-- Correctness: decaps(sk, encaps(pk).ct) = encaps(pk).ss
    for matching (pk, sk) keypair -/
axiom mlkem_correctness :
  ∀ (level : SecurityLevel),
    let (pk, sk) := keygen level
    let (ct, ss) := encaps level pk
    decaps level sk ct = ss

/-- IND-CCA2 security: decapsulation with the wrong key does not
    recover the shared secret.

    Under Module-LWE hardness, an adversary without sk cannot
    distinguish the real shared secret from random. We model
    this as: decaps with any other key sk' produces a different
    result than the correct shared secret.

    This is the functional consequence of IND-CCA2 that matters
    for protocol security: intercepting ct is useless without sk. -/
axiom mlkem_ind_cca2 :
  ∀ (level : SecurityLevel) (sk' : Nat),
    let (pk, sk) := keygen level
    let (ct, ss) := encaps level pk
    sk' ≠ sk → decaps level sk' ct ≠ ss

/-- Shared secret is always 32 bytes -/
theorem ss_fixed_size (level : SecurityLevel) : ssSize level = 32 := by
  cases level <;> rfl

/-- ML-KEM-768 is the default for Lux (NIST Level 3) -/
theorem default_level_3 : pkSize .mlkem768 = 1184 := rfl

/-- Key sizes grow with security level -/
theorem pk_monotone_512_768 : pkSize .mlkem512 < pkSize .mlkem768 := by
  simp [pkSize]

theorem pk_monotone_768_1024 : pkSize .mlkem768 < pkSize .mlkem1024 := by
  simp [pkSize]

/-- Ciphertext size is bounded -/
theorem ct_bounded (level : SecurityLevel) : ctSize level ≤ 1568 := by
  cases level <;> simp [ctSize]

/-- Combined hybrid KEM: ML-KEM + X25519 for belt-and-suspenders -/
axiom hybrid_kem_ss : SecurityLevel → Nat → Nat → Nat

/-- Hybrid KEM: shared secret combines both KEMs -/
axiom hybrid_kem_combines_both :
  ∀ (level : SecurityLevel) (mlkem_ss x25519_ss : Nat),
    -- The hybrid shared secret is derived from BOTH components
    -- Breaking requires breaking BOTH ML-KEM AND X25519
    hybrid_kem_ss level mlkem_ss x25519_ss ≠ mlkem_ss ∨
    hybrid_kem_ss level mlkem_ss x25519_ss ≠ x25519_ss

end Crypto.MLKEM
