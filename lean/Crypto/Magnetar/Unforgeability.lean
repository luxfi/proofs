/-
  Magnetar — Threshold Strong Unforgeability (TS-UF) reduction

  The threshold-signing unforgeability bound reduces to:
    1. The FIPS 205 SLH-DSA EUF-CMA bound (NIST 2024 analysis).
    2. The byte-wise Shamir VSS soundness over GF(257) — perfect
       information-theoretic secrecy below threshold (Shamir 1979).
    3. The reveal-and-aggregate trust model TCB caveat (the
       aggregator process is in the TCB for the brief window the
       master seed is reconstructed in memory).
    4. Standard random-oracle programming penalty for transcript
       binding under cSHAKE256.

  Maps to:
  - magnetar/SPEC.md §7 (Trust model — the v0.1 reveal-and-aggregate
    caveat)
  - magnetar/proofs/easycrypt/Magnetar_N1.ec
    `magnetar_n1_byte_equality` theorem (correctness, not yet
    unforgeability)
  - ref/go/pkg/magnetar/threshold.go + combine.go (the threshold
    sign + aggregator paths)

  Algebraic correctness of the underlying Shamir layer is discharged
  by `Crypto.Pulsar.Shamir.shamir_correct_at_target` (cross-cited;
  byte-wise GF(257) layer is identical between Pulsar and Magnetar).

  This file re-exports the headline reduction-statement consequence and
  states the named hardness assumptions that the cryptographic part of
  the proof reduces to.
-/

import Mathlib.Data.Nat.Defs
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import Crypto.Threshold_Lagrange
import Crypto.Pulsar.Shamir

namespace Crypto.Magnetar

open Polynomial

/-- The three Magnetar parameter levels mirror FIPS 205 SLH-DSA. -/
inductive ParamLevel : Type
  | SHAKE_192s : ParamLevel  -- NIST PQ Cat 3, recommended
  | SHAKE_192f : ParamLevel  -- NIST PQ Cat 3, fast variant
  | SHAKE_256s : ParamLevel  -- NIST PQ Cat 5
  deriving DecidableEq, Repr

/-- Per-level FIPS 205 SLH-DSA constants. Magnetar inherits these
    verbatim. -/
structure FipsSlhParams where
  n        : Nat   -- WOTS+ message length in bytes
  h        : Nat   -- total hypertree height
  d        : Nat   -- number of hypertree layers
  a        : Nat   -- FORS tree depth
  k        : Nat   -- FORS number of trees
  lambda   : Nat   -- security level in bits
  hn       : 0 < n
  hd       : 0 < d
  hd_div_h : h = d * (h / d)

/-- Threshold parameters (n, t) with 1 ≤ t ≤ n ≤ 256 (GF(257) cap). -/
structure ThresholdParams where
  n  : Nat
  t  : Nat
  ht : 0 < t
  hn : t ≤ n
  hcap : n ≤ 256

/-- The smallest prime > 255, used for byte-wise Shamir VSS. -/
def shamirPrime : Nat := 257

theorem shamirPrime_is_prime : Nat.Prime shamirPrime := by decide

-- ===========================================================================
-- Named cryptographic hardness assumptions for Magnetar.
-- These are NOT discharged in Lean — they ARE the academic-literature
-- foundation the security argument rests on.
-- ===========================================================================

/-- An adversary's advantage against a hardness problem, as a nonnegative
    quantity in units of 2^-k.

    Ordered and additive, which is what a bound of the form
    `adv ≤ a + b + c + d` requires. The previous model was `Unit`, in which
    every advantage is equal to every other and no bound is expressible — which
    is why the TS-UF statement below concluded `True`. -/
abbrev HardnessAdvantage := Nat

/-- SHAKE256 / cSHAKE256 collision resistance. NIST FIPS 202 + SP
    800-185 establish this as the standard hash-function security
    assumption Magnetar inherits. -/
axiom SHAKECollisionAdv (fp : FipsSlhParams) : HardnessAdvantage

/-- SHAKE256 / cSHAKE256 preimage resistance (second-preimage). -/
axiom SHAKEPreimageAdv (fp : FipsSlhParams) : HardnessAdvantage

/-- FIPS 205 SLH-DSA EUF-CMA advantage. The SPHINCS+ submission
    (Bernstein et al.) bounds this in terms of SHAKE collision +
    preimage resistance. NIST FIPS 205 §10.6 fixes the concrete
    parameters at SHAKE-192s/192f/256s. -/
axiom SLHDSAEUFCMAAdv (fp : FipsSlhParams) : HardnessAdvantage

/-- The aggregator-as-TCB caveat: v0.1 reveal-and-aggregate places
    the aggregator process in the TCB for the brief window the
    master seed is reconstructed. This is OPERATIONAL, not
    cryptographic — it captures the trust assumption explicitly. -/
axiom AggregatorTCBCaveat : HardnessAdvantage

-- ===========================================================================
-- Algebraic correctness re-export.
-- ===========================================================================

/-- **Magnetar byte-wise Shamir over GF(257) is correct.**

    Discharged: re-uses `Crypto.Pulsar.Shamir.shamir_correct_at_target`,
    which Magnetar inherits because the byte-wise Shamir over GF(257)
    construction is algebraically identical between Pulsar and
    Magnetar.

    The reconstruction identity holds at every committee size ≤ 256
    (the cap is 257-1 = 256 distinct non-zero evaluation points in
    GF(257)). -/
theorem magnetar_shamir_correct
    {F : Type*} [Field F] [DecidableEq F]
    (f : Polynomial F) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card) :
    f = Lagrange.interpolate s v (fun i => f.eval (v i)) :=
  Crypto.Pulsar.Shamir.shamir_correct_at_target f s v hvs degree_f_lt

-- ===========================================================================
-- TS-UF advantage bound for Magnetar.
-- ===========================================================================

/-- The advantage of the best adversary against Magnetar's threshold strong
    unforgeability at these parameters. Opaque: its value is whatever the
    reduction computes. -/
opaque magnetarTSUFAdv (fp : FipsSlhParams) (tp : ThresholdParams) :
    HardnessAdvantage

/-- The four named hardness advantages, summed. Free of `ThresholdParams` by
    construction — that is the substance of n-independence below. -/
noncomputable def MagnetarTSUFBound (fp : FipsSlhParams) : HardnessAdvantage :=
  SHAKECollisionAdv fp + SHAKEPreimageAdv fp + SLHDSAEUFCMAAdv fp
    + AggregatorTCBCaveat

/-- **TS-UF security of Magnetar.**

    Assumed, not proved here. `magnetar/PROOF-CLAIMS.md` §0 states that
    "Magnetar has no mechanized proof of any threshold property", and this
    corpus does not have one either — so the reduction's conclusion is recorded
    as an axiom, which is what an unmechanised reduction is.

    Maps to magnetar/SPEC.md §7 (the v0.1 trust model), whose aggregator-TCB
    caveat is the fourth summand. -/
axiom magnetar_tsuf (fp : FipsSlhParams) (tp : ThresholdParams) :
    magnetarTSUFAdv fp tp ≤ MagnetarTSUFBound fp

/-- **n-independence of the TS-UF bound.**

    The bound does not mention `ThresholdParams`, so one bound covers every
    threshold parameter set at a fixed FIPS level. This is the claim
    "the advantage is structural in the FIPS parameters, independent of n",
    and it follows from the shape of `MagnetarTSUFBound` rather than from
    re-wrapping the hypothesis. -/
theorem magnetar_tsuf_n_independent
    (fp : FipsSlhParams) (tp1 tp2 : ThresholdParams) :
    magnetarTSUFAdv fp tp1 ≤ MagnetarTSUFBound fp ∧
    magnetarTSUFAdv fp tp2 ≤ MagnetarTSUFBound fp :=
  ⟨magnetar_tsuf fp tp1, magnetar_tsuf fp tp2⟩

/- Hardness-family disjointness from Pulsar.

   `MagnetarTSUFBound` sums SHAKE collision resistance, SHAKE preimage
   resistance, FIPS 205 EUF-CMA and the aggregator-TCB caveat. No lattice
   advantage appears in it, while Pulsar's bound reduces to MLWE and MSIS. That
   is the cryptographic reason the Polaris profile (Pulsar || Corona ||
   Magnetar) is worth having: Pulsar and Corona are both Module-LWE, so Magnetar
   is its only family-disjoint leg.

   Not a theorem here. A theorem stood in this place of the form
   `(h : Bound) : Bound := h`, which returns its own hypothesis and so proves
   nothing about disjointness. Stating it properly quantifies over adversaries
   and reductions between problems; this model has neither, and the bound's
   independence from lattice hardness is visible in its definition instead.
-/

end Crypto.Magnetar
