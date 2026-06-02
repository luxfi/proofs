/-
  Shamir secret sharing over R_q -- algebraic core for Corona.

  Mirrors `~/work/lux/proofs/lean/Crypto/Pulsar/Shamir.lean` but with
  R_q replaced by Corona's polynomial ring (degree 256, modulus
  q = 0x1000000004A01).

  EasyCrypt-side companion: `~/work/lux/corona/proofs/easycrypt/Corona_N4.ec`
  uses the lemmas here via the named axioms `shamir_correct`,
  `reconstruct_linear`, `add_share_zeroR`.

  This file is structurally identical to the Pulsar Shamir theory --
  Corona and Pulsar share the same Lagrange-over-polynomial-ring
  algebra; only the underlying ring differs.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Crypto.Threshold_Lagrange

open Polynomial

namespace Crypto.Corona.Shamir

/-- The Lagrange-correctness theorem at a generic target point.
    Given a polynomial `f` of degree < |s|, evaluated at the |s|
    distinct points `v(s)`, Lagrange-interpolating the resulting
    values recovers `f`.

    EC counterpart: `Corona_N1.lagrange_inverse_eval` (at target 0).
    Refines: `~/work/lux/corona/primitives/shamir.go`
             `ShamirSecretSharingGeneral` + `ComputeLagrangeCoefficients`. -/
theorem shamir_correct_at_target
    {F : Type*} [Field F] [DecidableEq F]
    (f : Polynomial F) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card) :
    f = Lagrange.interpolate s v (fun i => f.eval (v i)) :=
  Crypto.Threshold.Lagrange.threshold_reconstructs_secret f s v hvs degree_f_lt

/-- Secret recovery at the standard Lagrange target 0.

    EC counterpart: `Corona_N4.shamir_correct` (specialized form).
    The Corona dealer picks a polynomial whose constant term is the
    secret; party i is handed share_i = P(i). Lagrange-interpolation at
    X = 0 over a quorum of t distinct evaluation points recovers the
    constant term. -/
theorem secret_recovery_at_zero
    {F : Type*} [Field F] [DecidableEq F]
    (f : Polynomial F) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card)
    (_hv0 : ∀ i ∈ s, v i ≠ 0) :
    (Lagrange.interpolate s v (fun i => f.eval (v i))).eval 0 = f.eval 0 :=
  (Crypto.Threshold.Lagrange.secret_recovery_at_zero f s v hvs degree_f_lt).symm

/-- Lagrange interpolation is linear in the per-party values.

    EC counterpart: `Corona_N4.reconstruct_linear`.
    Refines: `~/work/lux/corona/sign/sign.go` SignFinalize -- the
    z_sum aggregation step is linear in the per-party z_i values.

    Derived directly from `LinearMap.map_add` on the Lagrange
    interpolation map. -/
theorem combine_distributes_over_sum
    {F : Type*} [Field F] [DecidableEq F]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F) (a b : ι → F) :
    Lagrange.interpolate s v (a + b) =
      Lagrange.interpolate s v a +
      Lagrange.interpolate s v b :=
  Crypto.Threshold.Lagrange.combine_distributes_over_sum s v a b

/-- The right-identity of polynomial addition: `f + 0 = f`. Implicit
    in any AddCommMonoid instance; here we surface it for the EC
    bridge so the citation comment in `Corona_N4.ec` has a concrete
    target. -/
theorem add_share_zeroR
    {F : Type*} [Field F] [DecidableEq F] (f : Polynomial F) :
    f + 0 = f := by
  exact add_zero f

end Crypto.Corona.Shamir
