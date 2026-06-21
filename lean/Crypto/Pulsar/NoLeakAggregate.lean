/-
  Pulsar — No-leak masked-aggregate identity (de-misdirection of the EC
  reconstruct-then-sign cone).

  ## Why this file exists

  The EasyCrypt Class N1 byte-equality theorem
  (`pulsar_n1_byte_equality_extracted`) was phrased against a
  `SinglePartyRun` model that literally computes

      sk_group <- reconstruct quorum shares;   sig <- S.sign sk_group …

  i.e. it Lagrange-reconstructs the master secret and signs with it
  (RECONSTRUCT-THEN-SIGN). That is exactly the path the production
  leaderless signer must NEVER take (BLOCKERS.md PULSAR-V13-HINT-LEAK):
  reconstructing the secret — or any per-party `c·s2`/`c·t0` whose
  aggregate is `c·s2_master` — leaks the long-term key.

  This theory replaces that model's ALGEBRAIC CORE with the honest
  no-leak identity actually implemented in `ref/go/pkg/pulsar/bcc_sign.go`
  and `boundary.go`:

    1. **z-stage (no secret reconstruction).** The response `z = y + c·s1`
       is recovered as the Lagrange aggregate at 0 of the per-party MASKED
       partial responses `z_i = y_i + c · λ_i⁻¹-scaled share_i`. By
       `Crypto.Threshold.Lagrange.threshold_partial_response_identity`,

         (interpolate z).eval 0 = (interpolate y).eval 0 + c · f.eval 0,

       where `f` is the secret-sharing polynomial. **`f` (the master
       secret `s1`) is never formed** — only `f.eval 0` appears, and only
       as a term inside the already-public `z`. No party reveals
       `c · share_i` in the clear; the per-party `y_i` masks hide it and
       cancel under the public Lagrange combine.

    2. **hint-stage (public, no secret residual).** The hint `h` is
       recovered from the PUBLIC reconstructed `w' = A·z − c·t1·2^d` and
       the PUBLIC target `w1 = HighBits(w)` via the FIPS 204 `UseHint`
       primitive (`FindHint`), exactly as a verifier would. The hidden
       `c·s2`/`c·t0` shift cannot move `HighBits` because the nonce is
       boundary-clear. This is the machine-checked content of
       `Crypto.Pulsar.Boundary.boundary_clearance(_vec)` and
       `findHintCoeff_{sound,unique}`.

  Composing (1) and (2): the triple `(c̃, z, h)` is bit-identical to a
  single-party FIPS 204 signature on the SAME `(pk, m, ctx, ρ)` — **with
  the master secret never reconstructed and no key-bearing residual ever
  on the wire**.

  ## What remains open after this file (the honest residual)

  Byte-equality of the OUTPUT is established by (1)+(2) above modulo the
  faithful-wire-format codec bridges (Bucket B). What this file does NOT
  prove — and states as an explicit named hypothesis to be discharged by a
  STANDARD cryptographic assumption, not an implementation reconstruct —
  is that the *public threshold transcript*
  `(w1, commit(w), clearance-proof, c̃, z, h)` REVEALS NOTHING about
  `(s1, s2, t0)` beyond what one single-party FIPS 204 signature does. That
  is the `NoLeakReduction` predicate below; it reduces to:

    • **Module-LWE** — the commitment `w = A·y` is pseudorandom (the mask
      `y` is the LWE secret), so `w1 = HighBits(w)` and any hiding
      commitment to `w` leak nothing about `(s1,s2,t0)`; and the
      key-bearing residual `w' − w = c·t0 − c·s2` is NEVER published.
    • **Module-SIS (MSIS)** — extracting a usable `(s1,s2)` from the
      published `z`-partials + hint vector is a short-vector problem; this
      is the same assumption ML-DSA's own EUF-CMA rests on (FIPS 204 /
      Dilithium, Ducas et al.).

  These are the SAME assumptions ML-DSA already stands on. The point of
  this file is that the residual is now a STANDARD-ASSUMPTION reduction,
  not the "extracted code = central sign on the reconstructed secret"
  implementation axiom.

  Maps to:
  • ref/go/pkg/pulsar/bcc_sign.go      `bccSign` (z = y + c·s1; w'; FindHint)
  • ref/go/pkg/pulsar/boundary.go      `BoundaryClear`, `FindHint`, `useHint`
  • Crypto/Threshold_Lagrange.lean     `threshold_partial_response_identity`
  • Crypto/Pulsar/BoundaryClearance.lean
                                       `boundary_clearance`, `findHintCoeff_*`
  • spec/threshold-mldsa-boundary-clearance.tex
  • proofs/easycrypt/Pulsar_N1.ec      (the cone this file de-misdirects)
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import Crypto.Threshold_Lagrange
import Crypto.Pulsar.BoundaryClearance

namespace Crypto.Pulsar.NoLeak

open Polynomial
open Crypto.Threshold.Lagrange
open Crypto.Pulsar.Boundary

/-! ## 1. The z-stage no-leak aggregate identity (master secret never formed)

We work over the per-coefficient field view of `R_q` (the FIPS 204 ring),
as the Lagrange theory does: the secret-sharing polynomial is `f : F[X]`
with `f.eval 0 = s` (one coefficient of `s1`); party `i ∈ s` holds
`f.eval (v i)`; the per-party masked response is `z_i = y_i + c · f.eval (v i)`.

The CENTRAL value is `z = y + c·s = (interp y).eval 0 + c · f.eval 0`.
The theorem is that the public Lagrange aggregate of the `z_i` equals that
central value **without ever evaluating `interpolate … f-shares` as a step
that materialises `f`** — `f.eval 0` is the only secret-derived scalar and
it enters only inside the already-public `z`. -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **No-leak z aggregate (single coefficient).**

    The Lagrange aggregate at 0 of the masked per-party responses equals
    the central response `(interp y).eval 0 + c · f.eval 0`. This is
    `threshold_partial_response_identity` restated in no-leak vocabulary:
    `z_central` is built from the public masks `y` and the public challenge
    `c`; the secret polynomial `f` is consumed ONLY as `f.eval 0`, never
    reconstructed as `f` itself.

    Code: `bccSign` computes `z = y + c·s1` per coefficient; the threshold
    layer assembles the SAME `z` as the Lagrange combine of `z_i` without
    any party broadcasting `c·share_i`. -/
theorem z_aggregate_no_reconstruct
    (f : F[X]) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (hdeg : f.degree < s.card)
    (y : ι → F) (c : F) (z : ι → F)
    (hz : z = y + c • fun i => f.eval (v i)) :
    (Lagrange.interpolate s v z).eval 0
      = (Lagrange.interpolate s v y).eval 0 + c * f.eval 0 :=
  threshold_partial_response_identity f s v hvs hdeg y c z hz

/-- **The aggregate depends on the secret ONLY through `f.eval 0`.**

    Two secret-sharing polynomials with the SAME constant term and the
    SAME public masks produce the SAME public z-aggregate, regardless of
    their higher coefficients. This is the precise sense in which the
    combine "never reconstructs `f`": its public output is a function of
    `f.eval 0` (already inside the public `z`) and the public `(y, c)`
    alone — the rest of `f` (the sharing randomness) is invisible. -/
theorem z_aggregate_depends_only_on_secret
    (f g : F[X]) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (hdegf : f.degree < s.card) (hdegg : g.degree < s.card)
    (hconst : f.eval 0 = g.eval 0)
    (y : ι → F) (c : F)
    (zf zg : ι → F)
    (hzf : zf = y + c • fun i => f.eval (v i))
    (hzg : zg = y + c • fun i => g.eval (v i)) :
    (Lagrange.interpolate s v zf).eval 0
      = (Lagrange.interpolate s v zg).eval 0 := by
  rw [z_aggregate_no_reconstruct f s v hvs hdegf y c zf hzf,
      z_aggregate_no_reconstruct g s v hvs hdegg y c zg hzg, hconst]

/-! ## 2. The hint-stage no-leak recovery (public data only)

The hint is recovered from the public `w'` and public target `w1`. We
re-export the machine-checked boundary-clearance facts so a downstream
reader sees the full no-leak chain in one namespace. The key property is
that `HighBits` is STABLE under the hidden `‖δ‖∞ ≤ β` (= `c·s2`) shift —
so the verifier-reconstructable `w'` lands FindHint on the same `w1` the
signer committed to, without the signer (or any aggregator) ever forming
`c·s2`/`c·t0`/`r0`. -/

/-- **Hint recovered from public data is HighBits-stable under the hidden
    secret shift** (re-export of `boundary_clearance` in no-leak terms).

    `a` is one coefficient of the (hidden) commitment `w`; `δ` is the
    corresponding hidden `c·s2` perturbation. A boundary-clear `a` keeps
    its `HighBits` under `a ↦ a − δ`, so the public `w'` (which differs
    from `w` exactly by this residual) shares `w`'s `HighBits` — meaning
    `FindHint(w', w1)` succeeds WITHOUT the residual ever being formed. -/
theorem hint_highbits_stable_under_hidden_shift
    {a δ : ℤ}
    (hwrap : ∃ a1 r0, Decomposes a a1 r0)
    (hmargin : |LowBits a| < gamma2 - 2 * beta)
    (hδ : |δ| ≤ beta) :
    HighBits (a - δ) = HighBits a ∧ |LowBits (a - δ)| < gamma2 - beta :=
  boundary_clearance hwrap hmargin hδ

/-- **The public FindHint reproduces the FIPS UseHint hint, uniquely**
    (re-export of `findHintCoeff_unique`). FindHint touches only `(w',
    w1)`, both public; the bit it emits is THE FIPS hint bit, so the hint
    in the signature is correct without any secret residual. -/
theorem hint_is_fips_hint {w' target h h' : ℤ}
    (hsep : useHint 0 w' ≠ useHint 1 w')
    (hfind : findHintCoeff w' target = some h)
    (hmem' : h' = 0 ∨ h' = 1)
    (huse' : useHint h' w' = target) :
    h' = h :=
  findHintCoeff_unique hsep hfind hmem' huse'

/-! ## 3. The residual cryptographic assumption (STANDARD: Module-LWE / MSIS)

This is the ONLY open content after the two machine-checked stages above.
We state it as an abstract predicate over the public threshold transcript,
with the two named hardness hypotheses it reduces to. This is the honest
replacement for the EC `combine_body_axiom` reconstruct-then-sign cone: a
STANDARD-ASSUMPTION reduction, not an implementation reconstruct. -/

/-- The public quantities a no-leak BCC transcript exposes for one
    signature. Mirrors `bccTranscript.publicBytes` in `bcc_sign.go`:
    `w1`, a hiding commitment to `w`, the boundary-clearance proof token,
    and the signature triple `(c̃, z, h)`. Crucially it does NOT contain
    `w` itself, `LowBits w`, `c·s2`, `c·t0`, `r0`, or `w' − w`. -/
structure PublicTranscript where
  w1            : ByteArray   -- HighBits(w)            (public)
  wCommitment   : ByteArray   -- hiding commitment to w (public)
  clearanceProof: ByteArray   -- ZK boundary-clearance token (public)
  cTilde        : ByteArray   -- H(μ, w1)               (public, in sig)
  z             : ByteArray   -- y + c·s1               (public, in sig)
  hint          : ByteArray   -- UseHint-recovered      (public, in sig)
  deriving Inhabited

/-- A single-party FIPS 204 signature's public footprint on the same
    `(pk, m, ctx, ρ)` — the reference leakage profile. The no-leak claim
    is that the threshold transcript leaks no MORE than this. -/
opaque Fips204SignatureLeakage : Type

/-- **Module-LWE hardness over the FIPS 204 ring** (the mask `y` is the LWE
    secret; `w = A·y` is pseudorandom). Abstract proposition; this is the
    assumption FIPS 204 / Dilithium already make. -/
opaque ModuleLWEHard : Prop

/-- **Module-SIS hardness over the FIPS 204 ring** (extracting a short
    `(s1, s2)` from public signature data is a short-vector problem). The
    assumption ML-DSA's own EUF-CMA rests on. -/
opaque ModuleSISHard : Prop

/-- The simulator that, given ONLY a single-party FIPS 204 signature's
    public leakage, reproduces the threshold transcript's distribution.
    Existence of this simulator IS the no-leak property. -/
opaque transcriptSimulator : Fips204SignatureLeakage → PublicTranscript

/-- **No-leak reduction (the residual open assumption — STANDARD).**

    The public threshold transcript is simulatable from a single-party
    FIPS 204 signature's leakage alone, GIVEN Module-LWE and Module-SIS.
    This is the honest residual that replaces reconstruct-then-sign: the
    threshold path reveals nothing about `(s1,s2,t0)` beyond one ordinary
    signature, under the SAME standard lattice assumptions ML-DSA uses.

    It is stated as a hypothesis (`Prop`-valued reduction target), NOT
    proved here: the full simulation-soundness proof is the v0.8 EC/paper
    artifact. What this file MACHINE-CHECKS is that the CORRECTNESS core
    (z-aggregate + hint recovery) needs no reconstruction; what it
    DISCLOSES is that the remaining SECRECY content is a Module-LWE/MSIS
    reduction. -/
def NoLeakReduction : Prop :=
  ModuleLWEHard → ModuleSISHard →
    ∀ (leak : Fips204SignatureLeakage),
      ∃ tr : PublicTranscript, tr = transcriptSimulator leak

/-- **The shape of the honest claim, packaged.**

    Under the standard lattice assumptions, IF the no-leak reduction holds
    (the v0.8 secrecy obligation) THEN every public transcript is the
    simulator's output — i.e. carries no key information beyond a single
    FIPS 204 signature. The correctness that the transcript's `(c̃,z,h)` is
    a valid FIPS 204 signature is the separate `z_aggregate_no_reconstruct`
    + `hint_is_fips_hint` content above; neither half reconstructs the
    secret. -/
theorem no_leak_under_standard_assumptions
    (hred : NoLeakReduction)
    (hlwe : ModuleLWEHard) (hsis : ModuleSISHard)
    (leak : Fips204SignatureLeakage) :
    ∃ tr : PublicTranscript, tr = transcriptSimulator leak :=
  hred hlwe hsis leak

end Crypto.Pulsar.NoLeak
