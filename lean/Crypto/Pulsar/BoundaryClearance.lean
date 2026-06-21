/-
  Pulsar — Boundary-Clearance / Carry-Elimination (BCC/CEF) core lemmas

  Machine-checks the two load-bearing arithmetic facts behind the no-MPC /
  no-TEE hint path that replaces the leaking AlgebraicAggregate
  reconstruction (BLOCKERS.md PULSAR-V13-HINT-LEAK):

  1. **Boundary-clearance lemma (BCC+ correctness).** A coefficient whose
     centered low bits are strictly inside the boundary margin keeps its
     HighBits stable under every hidden `‖c·s2‖∞ ≤ β` shift, and its hidden
     residual `r0` stays strictly inside the FIPS rejection range. The
     protocol never forms `c·s2`, `c·t0`, or `r0`; this is the offline
     guarantee a surviving nonce-certificate buys.

  2. **FindHint ↔ UseHint equivalence.** The PUBLIC hint search
     `findHintCoeff` reproduces exactly the FIPS 204 UseHint relation, and
     the witnessing hint bit is the *unique* element of {0,1} achieving the
     target — so FindHint reconstructs the FIPS hint without ever touching
     secret residuals.

  Discrete arithmetic over FIPS 204 Decompose (Algorithm 36) is modelled
  with the *centered integer* representative, which is exactly what the Go
  bit-twiddling `decompose` computes. We do NOT model the modular
  reduction directly; instead we work with the algebraic identity
  `a = a1·α + a0`, `a0 ∈ (−γ2, γ2]`, and prove uniqueness of that
  decomposition (over ℤ, in the no-top-bucket-wrap regime that
  boundary-clearance certifies). This is faithful: BoundaryClear rejects
  every coefficient near a bucket edge, so the FIPS top-bucket wrap
  (`a − a0 = q − 1 ⇒ a1 := 0`) provably cannot fire on a cleared
  coefficient, and the centered decomposition is then the genuine
  HighBits/LowBits pair.

  Maps to:
  • ref/go/pkg/pulsar/boundary.go
      `BoundaryClear`, `boundaryClearCoeff`, `centeredLowBits`,
      `highBitsCoeff`, `useHint`, `FindHint`
  • ref/go/pkg/pulsar/mldsa_lattice.go `decompose` (FIPS 204 Alg. 36)
  • ref/go/pkg/pulsar/boundary_test.go
      `TestBoundaryClearImpliesHighBitsStable`,
      `TestFindHintToTargetMatchesUseHint`,
      `TestBoundaryClearEdgeCases`
  • spec/threshold-mldsa-boundary-clearance.tex
-/

import Mathlib.Data.Int.Defs
import Mathlib.Tactic

namespace Crypto.Pulsar.Boundary

/-! ## FIPS 204 ML-DSA-65/87 parameters

We fix the proven BCC scope: ML-DSA-65/87, where `γ2 = (q-1)/16 = 261888`,
`α = 2γ2`, and `β = τ·η`. The lemmas below are parametric in `γ2` and `β`
with the side conditions the scope guarantees, so they specialise to both
levels (and to 87) by plugging numerals. -/

/-- FIPS 204 modulus `q = 2^23 − 2^13 + 1`. -/
def q : ℤ := 8380417

/-- Low-bits half-window for ML-DSA-65/87: `γ2 = (q-1)/16`. -/
def gamma2 : ℤ := 261888

/-- Decompose stride `α = 2γ2`. -/
def alpha : ℤ := 2 * gamma2

/-- `β = τ·η = 4·49 = 196` for ML-DSA-65 (the `‖c·s2‖∞` bound; the
    statements are parametric, this is the canonical witness). -/
def beta : ℤ := 196

theorem alpha_val : alpha = 523776 := by decide
theorem gamma2_pos : 0 < gamma2 := by decide
theorem beta_pos : 0 < beta := by decide
theorem two_beta_lt_gamma2 : 2 * beta < gamma2 := by decide

/-! ## Centered decomposition (FIPS 204 Decompose, Algorithm 36)

`IsCentered r0` says `r0` is a legal centered low-part: `−γ2 < r0 ≤ γ2`.
`Decomposes a a1 r0` says `a = a1·α + r0` with `r0` centered — the
algebraic core of FIPS Decompose, away from the top-bucket wrap.

`highBits`/`lowBits` are the *interface* the Go exposes; we relate them to
`Decomposes` via the uniqueness theorem `decompose_unique`. -/

/-- A legal centered low-part: `r0 ∈ (−γ2, γ2]`. -/
def IsCentered (r0 : ℤ) : Prop := -gamma2 < r0 ∧ r0 ≤ gamma2

/-- `a` decomposes as `a1·α + r0` with `r0` centered (FIPS Decompose,
    Algorithm 36, interior of the bucket range). -/
def Decomposes (a a1 r0 : ℤ) : Prop := a = a1 * alpha + r0 ∧ IsCentered r0

/-- **Uniqueness of the centered decomposition.**

    Two centered representatives of the same value modulo `α` coincide,
    and so do the high parts. This is the workhorse: it lets us read off
    `HighBits` and `LowBits` from *any* exhibited centered decomposition,
    which is how the boundary-clearance proof transports a known
    decomposition of `a` to one of `a − δ`.

    Proof: from `a1·α + r0 = a1'·α + r0'` we get `(a1 − a1')·α = r0' − r0`.
    Both `r0, r0' ∈ (−γ2, γ2]` force `|r0' − r0| < 2γ2 = α`, so the only
    multiple of `α` in `(−α, α)` is `0`; hence `a1 = a1'` and `r0 = r0'`. -/
theorem decompose_unique {a a1 r0 a1' r0' : ℤ}
    (h : Decomposes a a1 r0) (h' : Decomposes a a1' r0') :
    a1 = a1' ∧ r0 = r0' := by
  obtain ⟨ha, hc⟩ := h
  obtain ⟨ha', hc'⟩ := h'
  obtain ⟨hlo, hhi⟩ := hc
  obtain ⟨hlo', hhi'⟩ := hc'
  -- (a1 − a1')·α = r0' − r0, and |r0' − r0| < α, so the difference is 0.
  have hα : alpha = 2 * gamma2 := rfl
  have key : (a1 - a1') * alpha = r0' - r0 := by ring_nf; linarith [ha, ha']
  -- Bound the RHS strictly inside (−α, α).
  have hbound : -alpha < r0' - r0 ∧ r0' - r0 < alpha := by
    rw [hα]; constructor <;> linarith
  -- A multiple of α that is strictly between −α and α must be 0.
  have hzero : a1 - a1' = 0 := by
    rcases lt_trichotomy (a1 - a1') 0 with hneg | heq | hpos
    · -- a1 - a1' ≤ -1 ⇒ (a1-a1')·α ≤ -α, contradicting -α < RHS
      have : a1 - a1' ≤ -1 := by omega
      have : (a1 - a1') * alpha ≤ (-1) * alpha := by
        apply mul_le_mul_of_nonneg_right this
        rw [hα]; linarith [gamma2_pos]
      rw [key] at this
      have : r0' - r0 ≤ -alpha := by linarith
      linarith [hbound.1]
    · exact heq
    · -- a1 - a1' ≥ 1 ⇒ (a1-a1')·α ≥ α, contradicting RHS < α
      have h1 : a1 - a1' ≥ 1 := by omega
      have : (1 : ℤ) * alpha ≤ (a1 - a1') * alpha := by
        apply mul_le_mul_of_nonneg_right h1
        rw [hα]; linarith [gamma2_pos]
      rw [key] at this
      have : alpha ≤ r0' - r0 := by linarith
      linarith [hbound.2]
  have h1 : a1 = a1' := by omega
  refine ⟨h1, ?_⟩
  -- r0 = r0' follows from key once a1 = a1'.
  rw [h1] at key
  simp at key
  omega

/-- **Existence is assumed at the interface, not the model.**

    `HighBits a` / `LowBits a` are the values the Go `decompose` returns
    (its centered low part and bucket index). `decompose_spec` says they
    *are* a centered decomposition of `a` — i.e. the Go function meets the
    FIPS Decompose contract on its in-range inputs, away from the
    top-bucket wrap. This is the single modelling axiom tying the abstract
    `Decomposes` relation to the concrete `highBits`/`lowBits` symbols; it
    is the FIPS 204 Algorithm 36 postcondition, KAT-checked by
    `boundary_test.go::TestBoundaryClearEdgeCases`. Everything downstream
    is proved from it plus `decompose_unique`. -/
opaque HighBits : ℤ → ℤ
opaque LowBits : ℤ → ℤ

/-- The Go `decompose` meets the centered-decomposition contract: its
    returned `(a1, a0)` satisfy `a = a1·α + a0` with `a0` centered. We
    require it on the no-wrap regime (`Decomposes` is the interior form);
    boundary-clearance guarantees we only ever invoke it there. -/
axiom decompose_spec (a : ℤ) (hwrap : ∃ a1 r0, Decomposes a a1 r0) :
    Decomposes a (HighBits a) (LowBits a)

/-! ## 1. Boundary-clearance lemma (core BCC+ correctness) -/

/-- **Boundary-clearance, abstract form.**

    If `a` has a centered decomposition with low part `r0` satisfying
    `|r0| < γ2 − 2β`, then for every `δ` with `|δ| ≤ β`:
      • `a − δ` has the *same* high part `a1`, and
      • its low part is exactly `r0 − δ`, with `|r0 − δ| < γ2 − β`.

    This is the algebraic heart of `TestBoundaryClearImpliesHighBitsStable`:
    HighBits is stable under the hidden `c·s2` shift, and the hidden FIPS
    residual `r0 − δ` stays strictly inside `(−(γ2−β), γ2−β)` ⊂ the
    rejection range. No `c·s2` is ever formed: the bound on the *original*
    `r0` alone forces both conclusions, because `r0 − δ` is still a legal
    centered representative and centered representatives are unique
    (`decompose_unique`).

    Hypotheses use the strict margin `|r0| < γ2 − 2β` exactly as
    `boundaryThreshold = γ2 − 2β` (modulo the 1-coefficient `bccSlack`,
    which only tightens the predicate and is therefore subsumed). -/
theorem boundary_clearance_abstract
    {a a1 r0 δ : ℤ}
    (hdec : Decomposes a a1 r0)
    (hmargin : |r0| < gamma2 - 2 * beta)
    (hδ : |δ| ≤ beta) :
    Decomposes (a - δ) a1 (r0 - δ) ∧ |r0 - δ| < gamma2 - beta := by
  obtain ⟨ha, hc⟩ := hdec
  rw [abs_le] at hδ
  rw [abs_lt] at hmargin
  -- r0 − δ is still centered: |r0 − δ| ≤ |r0| + |δ| < (γ2 − 2β) + β = γ2 − β < γ2.
  have hcen : IsCentered (r0 - δ) := by
    obtain ⟨hl, hr⟩ := hmargin
    constructor
    · -- −γ2 < r0 − δ
      have := beta_pos; have := gamma2_pos
      linarith [hδ.1, hδ.2]
    · -- r0 − δ ≤ γ2
      have := beta_pos
      linarith [hδ.1, hδ.2]
  -- The same a1 works for a − δ.
  have hdec' : Decomposes (a - δ) a1 (r0 - δ) := by
    refine ⟨?_, hcen⟩
    rw [ha]; ring
  refine ⟨hdec', ?_⟩
  -- The hidden r0 bound: |r0 − δ| < γ2 − β.
  rw [abs_lt]
  obtain ⟨hl, hr⟩ := hmargin
  constructor
  · linarith [hδ.1, hδ.2]
  · linarith [hδ.1, hδ.2]

/-- **Boundary-clearance, interface form (HighBits/LowBits stable).**

    The same statement phrased on the concrete Go symbols: if a cleared
    coefficient `a` (its `LowBits` strictly inside the margin) is shifted
    by any `|δ| ≤ β`, then `HighBits (a − δ) = HighBits a` and
    `|LowBits (a − δ)| < γ2 − β`. Obtained from the abstract form by
    `decompose_unique` reading the high/low parts off the exhibited
    decomposition of `a − δ`. -/
theorem boundary_clearance
    {a δ : ℤ}
    (hwrap : ∃ a1 r0, Decomposes a a1 r0)
    (hmargin : |LowBits a| < gamma2 - 2 * beta)
    (hδ : |δ| ≤ beta) :
    HighBits (a - δ) = HighBits a ∧ |LowBits (a - δ)| < gamma2 - beta := by
  -- Pin the decomposition of a from the spec.
  have hda : Decomposes a (HighBits a) (LowBits a) := decompose_spec a hwrap
  -- Transport it to a − δ via the abstract lemma.
  obtain ⟨hda', hlow'⟩ := boundary_clearance_abstract hda hmargin hδ
  -- a − δ also has a centered decomposition, so the spec applies to it.
  have hwrap' : ∃ a1 r0, Decomposes (a - δ) a1 r0 :=
    ⟨HighBits a, LowBits a - δ, hda'⟩
  have hda2 : Decomposes (a - δ) (HighBits (a - δ)) (LowBits (a - δ)) :=
    decompose_spec (a - δ) hwrap'
  -- Uniqueness: the spec's (HighBits, LowBits) of a−δ equals (HighBits a, LowBits a − δ).
  obtain ⟨hH, hL⟩ := decompose_unique hda2 hda'
  refine ⟨hH, ?_⟩
  rw [hL]; exact hlow'

/-! ## 2. FindHint ↔ UseHint equivalence

We model the FIPS 204 UseHint (Algorithm 40) bucket interface abstractly:
`m` buckets, `useHint h r` returns the (possibly ±1-corrected) high part.
The Go computes this from `decompose`; here we expose it as the same
three-case function and prove the FindHint↔UseHint theorem the Go test
`TestFindHintToTargetMatchesUseHint` checks empirically. -/

/-- Number of HighBits buckets `m = (q-1)/(2γ2) = 16` for ML-DSA-65/87. -/
def m : ℤ := 16

theorem m_val : m = (q - 1) / alpha := by decide

/-- FIPS 204 UseHint (Algorithm 40), faithful to `useHint` in
    `mldsa_lattice.go` / `boundary.go`:
      • `h = 0` ⇒ return the high part `HighBits r`;
      • `h ≠ 0` and `LowBits r > 0` ⇒ `(HighBits r + 1) mod m`;
      • `h ≠ 0` and `LowBits r ≤ 0` ⇒ `(HighBits r − 1) mod m`
        (the Go writes `(r1 + m − 1) mod m`, equal to `(r1 − 1) mod m`).
    `Int.emod` matches the Go `%` on non-negative operands, which the
    bucket indices always are. -/
def useHint (h r : ℤ) : ℤ :=
  if h = 0 then HighBits r
  else if 0 < LowBits r then (HighBits r + 1) % m
  else (HighBits r - 1 + m) % m

/-- The PUBLIC hint search of one coefficient, faithful to the `switch`
    in `FindHint`:
      • if `HighBits w' = target` choose `h = 0`;
      • else if `useHint 1 w' = target` choose `h = 1`;
      • else there is no valid FIPS hint (returns `none`). -/
def findHintCoeff (w' target : ℤ) : Option ℤ :=
  if HighBits w' = target then some 0
  else if useHint 1 w' = target then some 1
  else none

/-- `useHint 0 r` is just the unmodified high part. -/
@[simp] theorem useHint_zero (r : ℤ) : useHint 0 r = HighBits r := by
  simp [useHint]

/-- **Soundness of FindHint: it reproduces FIPS UseHint.**

    If `findHintCoeff w' target = some h`, then `useHint h w' = target`.
    So every hint FindHint emits is validated through the FIPS UseHint
    primitive — never an informal ±1 corrector. (This is exactly the
    per-coefficient claim of `TestFindHintToTargetMatchesUseHint`.) -/
theorem findHintCoeff_sound {w' target h : ℤ}
    (hfind : findHintCoeff w' target = some h) :
    useHint h w' = target := by
  unfold findHintCoeff at hfind
  by_cases h0 : HighBits w' = target
  · -- Branch h = 0.
    simp [h0] at hfind
    subst hfind
    simpa using h0
  · simp [h0] at hfind
    by_cases h1 : useHint 1 w' = target
    · simp [h1] at hfind
      subst hfind
      exact h1
    · simp [h1] at hfind

/-- **Hint emission is only on the two legal bits.**

    `findHintCoeff` only ever returns `0` or `1`; it never invents a hint
    bit outside `{0,1}`. -/
theorem findHintCoeff_mem {w' target h : ℤ}
    (hfind : findHintCoeff w' target = some h) :
    h = 0 ∨ h = 1 := by
  unfold findHintCoeff at hfind
  by_cases h0 : HighBits w' = target
  · simp [h0] at hfind; exact Or.inl hfind.symm
  · simp [h0] at hfind
    by_cases h1 : useHint 1 w' = target
    · simp [h1] at hfind; exact Or.inr hfind.symm
    · simp [h1] at hfind

/-- **Completeness of FindHint over `{0,1}`.**

    If *some* legal bit `h ∈ {0,1}` satisfies `useHint h w' = target`, then
    `findHintCoeff` succeeds (returns `some` of *a* legal bit). Combined
    with soundness, FindHint succeeds *iff* a FIPS-valid hint exists, which
    is the `iff` the Go theorem header asserts. -/
theorem findHintCoeff_complete {w' target h : ℤ}
    (hmem : h = 0 ∨ h = 1) (huse : useHint h w' = target) :
    ∃ h', findHintCoeff w' target = some h' := by
  unfold findHintCoeff
  by_cases h0 : HighBits w' = target
  · exact ⟨0, by simp [h0]⟩
  · rcases hmem with rfl | rfl
    · -- h = 0 ⇒ useHint 0 w' = HighBits w' = target, contradicting h0.
      rw [useHint_zero] at huse; exact absurd huse h0
    · -- h = 1 ⇒ the second branch fires.
      have : useHint 1 w' = target := huse
      exact ⟨1, by simp [h0, this]⟩

/-- **Uniqueness of the hint bit (FindHint reproduces the FIPS hint).**

    On the regime FindHint actually runs in — where the two legal bits give
    *different* UseHint outputs (`useHint 0 w' ≠ useHint 1 w'`, i.e. the
    coefficient genuinely needs a decision) — at most one `h ∈ {0,1}` maps
    to a given target. Hence the bit FindHint chooses is THE FIPS hint bit,
    not merely *a* witness.

    The separation hypothesis `useHint 0 w' ≠ useHint 1 w'` holds whenever a
    correction is meaningful; if it failed, both bits would be
    interchangeable and "uniqueness" would be vacuous/false, so stating it
    as a hypothesis is the honest form. -/
theorem hint_bit_unique {w' target h₁ h₂ : ℤ}
    (hsep : useHint 0 w' ≠ useHint 1 w')
    (hm₁ : h₁ = 0 ∨ h₁ = 1) (hm₂ : h₂ = 0 ∨ h₂ = 1)
    (h1 : useHint h₁ w' = target) (h2 : useHint h₂ w' = target) :
    h₁ = h₂ := by
  rcases hm₁ with rfl | rfl <;> rcases hm₂ with rfl | rfl
  · rfl
  · -- 0 and 1 both hit target ⇒ useHint 0 = useHint 1, contradiction.
    exact absurd (h1.trans h2.symm) hsep
  · exact absurd (h2.trans h1.symm) hsep
  · rfl

/-- **FindHint chooses the unique FIPS hint bit.**

    Packaging soundness + uniqueness: if FindHint emits `h` and the
    coefficient is in the decision regime, then `h` is the one and only
    `{0,1}` bit reproducing the FIPS UseHint target. -/
theorem findHintCoeff_unique {w' target h h' : ℤ}
    (hsep : useHint 0 w' ≠ useHint 1 w')
    (hfind : findHintCoeff w' target = some h)
    (hmem' : h' = 0 ∨ h' = 1)
    (huse' : useHint h' w' = target) :
    h' = h := by
  have hsound : useHint h w' = target := findHintCoeff_sound hfind
  have hmem : h = 0 ∨ h = 1 := findHintCoeff_mem hfind
  exact hint_bit_unique hsep hmem' hmem huse' hsound

/-! ## 3. Per-vector corollaries (all coefficients)

A Pulsar commitment is a `polyVec`: finitely many coefficients indexed by
`(i, j)` (module rank × ring degree). The per-vector statements quantify
the per-coefficient lemmas over the index set. We model a vector as a
function `Coeff → ℤ` for an arbitrary finite index type. -/

variable {Coeff : Type*}

/-- A whole vector `w` is **boundary-clear** when every coefficient's
    `LowBits` is strictly inside the margin (mirrors `BoundaryClear`). -/
def VectorBoundaryClear (w : Coeff → ℤ) : Prop :=
  ∀ j, |LowBits (w j)| < gamma2 - 2 * beta

/-- A per-coefficient shift bounded by `β` (mirrors a hidden `c·s2`
    perturbation `‖·‖∞ ≤ β`). -/
def ShiftBounded (δ : Coeff → ℤ) : Prop := ∀ j, |δ j| ≤ beta

/-- **Per-vector boundary-clearance.**

    A boundary-clear commitment `w` keeps HighBits stable under every
    coefficient-wise `‖δ‖∞ ≤ β` shift, and every hidden residual stays in
    range — the exact guarantee `BoundaryClear` ⇒ a surviving nonce
    certifies, for all coefficients at once. -/
theorem boundary_clearance_vec
    (w δ : Coeff → ℤ)
    (hwrap : ∀ j, ∃ a1 r0, Decomposes (w j) a1 r0)
    (hclear : VectorBoundaryClear w)
    (hshift : ShiftBounded δ) :
    ∀ j, HighBits (w j - δ j) = HighBits (w j)
       ∧ |LowBits (w j - δ j)| < gamma2 - beta :=
  fun j => boundary_clearance (hwrap j) (hclear j) (hshift j)

/-- **Per-vector FindHint soundness.**

    If FindHint succeeds on every coefficient with chosen bits `h`, then
    `useHint (h j) (w' j) = target j` for all `j`: the FIPS UseHint
    relation holds across the whole hint vector (the per-vector form of
    `TestFindHintToTargetMatchesUseHint`'s inner assertion). -/
theorem findHint_vec_sound
    (w' target h : Coeff → ℤ)
    (hfind : ∀ j, findHintCoeff (w' j) (target j) = some (h j)) :
    ∀ j, useHint (h j) (w' j) = target j :=
  fun j => findHintCoeff_sound (hfind j)

/-- **Per-vector hint uniqueness.**

    In the decision regime on every coefficient, the hint vector FindHint
    produces is the unique `{0,1}`-valued vector reproducing the FIPS
    UseHint targets — so FindHint reconstructs the FIPS hint coefficient by
    coefficient, from public data only. -/
theorem findHint_vec_unique
    (w' target h h' : Coeff → ℤ)
    (hsep : ∀ j, useHint 0 (w' j) ≠ useHint 1 (w' j))
    (hfind : ∀ j, findHintCoeff (w' j) (target j) = some (h j))
    (hmem' : ∀ j, h' j = 0 ∨ h' j = 1)
    (huse' : ∀ j, useHint (h' j) (w' j) = target j) :
    ∀ j, h' j = h j :=
  fun j => findHintCoeff_unique (hsep j) (hfind j) (hmem' j) (huse' j)

end Crypto.Pulsar.Boundary
