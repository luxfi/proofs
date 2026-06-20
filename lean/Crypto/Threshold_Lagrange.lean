/-
  Threshold — Lagrange interpolation identity for threshold correctness.

  This is the algebraic heart of the threshold-to-single-party reduction
  for Pulsar (ML-DSA threshold) and Corona (Module-LWE threshold). Both
  are Module-LWE schemes; the Shamir-over-ring structure below is shared.

  Both schemes share the structure:

    • The dealer commits to a polynomial f ∈ F[X], f.degree < t, with
      f.eval 0 = s (the secret).
    • Each of n parties holds the share f.eval i for distinct non-zero
      i ∈ F.
    • Any t parties can reconstruct s = f.eval 0 by Lagrange interpolation.
    • Per-party "partial signatures" z_i = y_i + c · share_i sum (via
      Lagrange coefficients) to the single-party value z = y + c · s.

  The load-bearing fact is `threshold_reconstructs_secret`: for every
  polynomial of degree < t evaluated at any t distinct non-zero points,
  the Lagrange interpolation evaluated at 0 returns the constant term.
  This is `Polynomial.Lagrange.eq_interpolate` applied at 0 — no admit,
  no axiom.

  Maps to:
    • ref/go/pkg/pulsar/shamir.go        ShamirSecretSharingGeneral
    • ref/go/pkg/pulsar/threshold.go     ThresholdSigner.Round1/Round2/Combine
    • corona/sign/sign.go                Combine (Corona M-LWE params)
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

namespace Crypto.Threshold.Lagrange

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Threshold reconstruction identity.**

    Let `f ∈ F[X]` have `f.degree < #s`. Let `v : ι → F` be an injective
    indexing of the evaluation points (each party's share index, all
    distinct). Then the Lagrange interpolation of `f`'s evaluations
    through `v` is exactly `f`. In particular, evaluating that
    interpolation at `0` recovers `f.eval 0` — the constant term, which
    is the threshold-shared secret.

    This is the algebraic content the Pulsar/Corona `Combine` step
    relies on: combining t per-party partial values via Lagrange
    coefficients reproduces the single-party value bit-for-bit. -/
theorem threshold_reconstructs_secret
    (f : F[X]) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card) :
    f = Lagrange.interpolate s v (fun i => f.eval (v i)) :=
  Lagrange.eq_interpolate hvs degree_f_lt

/-- **Constant-term recovery at zero.**

    Specializes the reconstruction identity to evaluation at 0: the
    Lagrange interpolation evaluated at 0 returns the secret. This is
    the load-bearing equality for the Pulsar Class N1 reduction. -/
theorem secret_recovery_at_zero
    (f : F[X]) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card) :
    f.eval 0 = (Lagrange.interpolate s v (fun i => f.eval (v i))).eval 0 := by
  congr 1
  exact threshold_reconstructs_secret f s v hvs degree_f_lt

/-- **Combine-step linearity.**

    The Pulsar / Corona `Combine` operation is linear in each per-party
    contribution: combining partial responses z_i = y_i + c · share_i
    via Lagrange coefficients distributes over the addition. The
    threshold-equal-single-party byte equality reduces to this lemma
    plus `threshold_reconstructs_secret`.

    In Lean form: applying the Lagrange interpolation to a sum of
    per-party functions equals the sum of the Lagrange interpolations.
    Mathlib's `LinearMap.map_add` / `interpolate` is itself an
    `F-linear map` so this is `map_add` on the `interpolate` LinearMap. -/
theorem combine_distributes_over_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F) (a b : ι → F) :
    Lagrange.interpolate s v (a + b) =
      Lagrange.interpolate s v a + Lagrange.interpolate s v b :=
  (Lagrange.interpolate s v).map_add a b

/-- **Scaling under a public scalar.**

    A per-party scaling by a public scalar c (the Fiat-Shamir
    challenge in Pulsar; the round challenge in Corona) commutes with
    the Lagrange combine. -/
theorem combine_distributes_over_smul
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F) (c : F) (a : ι → F) :
    Lagrange.interpolate s v (c • a) =
      c • Lagrange.interpolate s v a :=
  (Lagrange.interpolate s v).map_smul c a

/-- **The threshold partial-response identity** (composition of the
    three lemmas above).

    Given a Shamir polynomial f with f.eval 0 = secret, and per-party
    masks y_i + c · share_i (where share_i = f.eval (v i)):

      Σ λ_i · z_i = y + c · secret

    Proof structure:
      • `combine_distributes_over_sum` splits the y-part and the
        c · share-part of z_i.
      • `combine_distributes_over_smul` pulls c out of the share-part.
      • `secret_recovery_at_zero` collapses the share-part's Lagrange
        sum to f.eval 0 = secret.

    The y-part and c · secret components reconstruct exactly the
    single-party value z = y + c · secret. This is the byte-equality
    invariant the Pulsar Combine routine implements (and that
    `coronaThreshold.Combine` implements for the R-LWE variant).

    The full byte-by-byte single-party-equality theorem composes this
    algebraic identity with the FIPS 204 verifier dispatch axiom in
    OutputInterchange.lean. -/
theorem threshold_partial_response_identity
    (f : F[X]) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card)
    (y : ι → F) (c : F)
    (z : ι → F) (hz : z = y + c • fun i => f.eval (v i)) :
    (Lagrange.interpolate s v z).eval 0 =
      (Lagrange.interpolate s v y).eval 0 + c * f.eval 0 := by
  -- Unfold z via the given hypothesis
  subst hz
  -- Lagrange interpolation is linear: split the sum, pull out the scalar
  rw [combine_distributes_over_sum]
  rw [combine_distributes_over_smul]
  -- Evaluate the sum at 0
  rw [Polynomial.eval_add, Polynomial.eval_smul]
  -- The share-part Lagrange interpolation IS f itself by `eq_interpolate`
  have hshare :
      Lagrange.interpolate s v (fun i => f.eval (v i)) = f :=
    (threshold_reconstructs_secret f s v hvs degree_f_lt).symm
  rw [hshare, smul_eq_mul]
  -- Now both sides match: y-eval + c · f.eval 0

/-- **No-mask specialization** (threshold BLS partial-signature form).

    BLS threshold partial signatures carry no per-party nonce
    (`y_i = 0`): party `i` contributes `σ_i = c · share_i` where
    `share_i = f.eval (v i)`. Combining the partials via Lagrange
    coefficients reproduces the single-party value `c · secret =
    c · f.eval 0` exactly.

    This is `threshold_partial_response_identity` with `y = 0`: the
    `y`-part's Lagrange interpolation is the zero polynomial (the
    interpolation map is `F`-linear, so it sends the zero function to
    `0`), and `(0 : F[X]).eval 0 = 0` makes the masking term vanish.

    Discharges the EC AXIOM 4 bridge cited at `Crypto/BLS.lean`
    (`BLS_Threshold_N1.ec:148`, Boldyreva 2003 threshold BLS) — the
    "Lagrange identity over `F_r` specialized to no-y-mask form". -/
theorem threshold_partial_response_identity_no_mask
    (f : F[X]) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card)
    (c : F) (z : ι → F) (hz : z = c • fun i => f.eval (v i)) :
    (Lagrange.interpolate s v z).eval 0 = c * f.eval 0 := by
  -- Re-express z with an explicit zero mask so the general identity applies.
  have hz' : z = (0 : ι → F) + c • fun i => f.eval (v i) := by rw [hz, zero_add]
  -- The Lagrange interpolation of the zero mask is the zero polynomial.
  have hzero : Lagrange.interpolate s v (0 : ι → F) = 0 :=
    (Lagrange.interpolate s v).map_zero
  have h := threshold_partial_response_identity f s v hvs degree_f_lt 0 c z hz'
  rw [h, hzero, Polynomial.eval_zero, zero_add]

end Crypto.Threshold.Lagrange
