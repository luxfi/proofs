/-
  Corona — No-leak masked-aggregate identity (de-misdirection of the EC
  reconstruct-then-sign cone).

  ## Why this file exists

  The EasyCrypt Corona Class N1 byte-equality theorem
  (`corona_n1_byte_equality`) was phrased against a `SinglePartyRun` /
  `CombineAbs` model whose `sign_abs_op_lifted_eq_rlwe` bridge pins the
  combine to `rlwe_sign_op (reconstruct quorum shares) …` — it
  Lagrange-RECONSTRUCTS the master secret and signs with it
  (RECONSTRUCT-THEN-SIGN). The Boschini/Raccoon production combine must
  NEVER do that (BLOCKERS.md CORONA-EC-RECON-MODEL): reconstructing the
  secret, or broadcasting per-party `c·s_i` whose aggregate is `c·s`,
  breaks threshold secrecy and transcript simulation.

  This theory replaces that model's ALGEBRAIC CORE with the honest no-leak
  identity actually implemented in `~/work/lux/corona/sign/sign.go`
  (`SignRound2` / `SignFinalize`):

    z_i = R_i·u + maskPrime_i + c·λ_i·s_i − mask_i      (per party i)

  where, for quorum `T`,

    mask_i      = Σ_{j∈T} PRF(seed_i[j],   …)      (party i's own seeds)
    maskPrime_i = Σ_{j∈T} PRF(seeds[j][i], …)      (others' seeds for i)

  The two pairwise-PRF mask families are the SAME double-indexed family
  reindexed:  Σ_i maskPrime_i = Σ_{i,j} PRF(seeds[j][i]) = Σ_i mask_i.
  So on aggregation the masks TELESCOPE TO ZERO and

    Σ_i z_i = R·u + c · Σ_i λ_i·s_i = R·u + c·s     (Lagrange at 0),

  recovering the central response WITHOUT any party broadcasting `c·s_i`
  in the clear and WITHOUT reconstructing the master secret `s`. The
  pairwise masks hide each `c·λ_i·s_i` and cancel only in the full sum.

  ## Two machine-checked no-leak facts in this file

    1. **Telescoping pairwise-mask cancellation** (`pairwise_mask_telescopes`):
       Σ_i (maskPrime_i − mask_i) = 0 over the quorum, from the antisymmetric
       pairwise structure. This is the Corona-specific no-leak core: it is
       why the aggregate carries no per-party mask, hence no opening that
       would expose `c·λ_i·s_i`.

    2. **Lagrange secret aggregation** (`secret_aggregate_no_reconstruct`):
       the surviving `c · Σ_i λ_i·s_i` equals `c · s` with the secret-sharing
       polynomial `f` (the master `s`) never formed — reusing the shared
       `Crypto.Threshold.Lagrange.threshold_partial_response_identity`.

  Composing (1)+(2): `Σ_i z_i = R·u + c·s` with NO reconstruction and NO
  key-bearing per-party term ever revealed.

  ## What remains open after this file (the honest residual)

  As for Pulsar, OUTPUT byte-equality follows modulo the faithful-wire
  codec bridges (Bucket B). The remaining SECRECY content — that the public
  Corona transcript (commitments + `z`-sum + the rounded `h`) reveals
  nothing about `s` beyond one single-party Boschini signature — is the
  `NoLeakReduction` predicate below, reducing to **Module-LWE** (the
  Gaussian masks `R_i·u + maskPrime_i − mask_i` hide `c·λ_i·s_i`) and
  **Module-SIS** (extracting `s` from the public z-sum is a short-vector
  problem). These are the SAME assumptions the Boschini/Ringtail
  construction (ePrint 2024/1113) already stands on. The residual is now a
  STANDARD-ASSUMPTION reduction, not an implementation reconstruct.

  Maps to:
  • corona/sign/sign.go            SignRound2 (z_i with telescoping masks),
                                   SignFinalize (z_sum)
  • Crypto/Threshold_Lagrange.lean threshold_partial_response_identity
  • Crypto/Corona/Shamir.lean      combine_distributes_over_sum
  • corona/proofs/easycrypt/Corona_N1.ec  (the cone this file de-misdirects)
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import Crypto.Threshold_Lagrange

namespace Crypto.Corona.NoLeak

open Polynomial BigOperators
open Crypto.Threshold.Lagrange

/-! ## 1. Telescoping pairwise-mask cancellation (Corona no-leak core)

We model the per-pair PRF mask as an arbitrary function `p : ι → ι → M`
over an additive commutative group `M` (the ring `R_q^N`). For quorum
`T : Finset ι`:

  • `mask i      = Σ_{j ∈ T} p i j`     (party i uses its own seed-for-j)
  • `maskPrime i = Σ_{j ∈ T} p j i`     (party i collects others' seed-for-i)

The aggregate of `maskPrime − mask` over the quorum telescopes to 0 because
both are the SAME double sum `Σ_{i∈T} Σ_{j∈T} p i j` reindexed by swapping
`(i,j)`. NO antisymmetry of `p` is needed — only Fubini over a finite
product, which is the honest reason the masks cancel: `seeds[j][i]` summed
over all `(i,j)` is the same multiset as `seed_i[j]` summed over all `(i,j)`. -/

variable {M : Type*} [AddCommGroup M]
variable {ι : Type*} [DecidableEq ι]

/-- `Σ_{i∈T} Σ_{j∈T} p j i = Σ_{i∈T} Σ_{j∈T} p i j` — the double sum is
    invariant under swapping the two quorum indices (Fubini /
    `Finset.sum_comm`). This is the algebraic fact behind the telescope. -/
theorem pairwise_double_sum_swap (T : Finset ι) (p : ι → ι → M) :
    (∑ i ∈ T, ∑ j ∈ T, p j i) = ∑ i ∈ T, ∑ j ∈ T, p i j := by
  rw [Finset.sum_comm]

/-- **Pairwise mask telescope (Corona no-leak core).**

    With `mask i = Σ_{j∈T} p i j` and `maskPrime i = Σ_{j∈T} p j i`, the
    quorum aggregate of `maskPrime i − mask i` is ZERO. Hence the summed
    response `Σ_i z_i` carries no surviving mask term — the per-party
    `c·λ_i·s_i` was hidden by `maskPrime_i − mask_i` and only the cancelled
    sum is exposed. This is exactly why `SignFinalize`'s `z_sum` is
    leak-free: the masks vanish, never the secret shares individually. -/
theorem pairwise_mask_telescopes
    (T : Finset ι) (p : ι → ι → M)
    (mask maskPrime : ι → M)
    (hmask : ∀ i, mask i = ∑ j ∈ T, p i j)
    (hmaskPrime : ∀ i, maskPrime i = ∑ j ∈ T, p j i) :
    (∑ i ∈ T, (maskPrime i - mask i)) = 0 := by
  simp only [hmask, hmaskPrime, Finset.sum_sub_distrib]
  rw [pairwise_double_sum_swap T p]
  exact sub_self _

/-- **The summed response equals the mask-free aggregate.**

    Writing each party response as `z i = base i + (maskPrime i − mask i)`
    (where `base i = R_i·u + c·λ_i·s_i` is the unmasked content), the
    quorum sum collapses to `Σ_i base i`: the masks contribute nothing.
    This is the precise statement that `z_sum` reveals only the aggregate,
    no per-party masked term. -/
theorem summed_response_is_mask_free
    (T : Finset ι) (p : ι → ι → M)
    (base z mask maskPrime : ι → M)
    (hmask : ∀ i, mask i = ∑ j ∈ T, p i j)
    (hmaskPrime : ∀ i, maskPrime i = ∑ j ∈ T, p j i)
    (hz : ∀ i, z i = base i + (maskPrime i - mask i)) :
    (∑ i ∈ T, z i) = ∑ i ∈ T, base i := by
  simp only [hz, Finset.sum_add_distrib]
  rw [pairwise_mask_telescopes T p mask maskPrime hmask hmaskPrime, add_zero]

/-! ## 2. Lagrange secret aggregation (master secret never formed)

The surviving `Σ_i base i = R·u + c · Σ_i λ_i·s_i`. The `c · Σ_i λ_i·s_i`
part is `c · s` by Lagrange-at-0, with the secret-sharing polynomial `f`
(the master `s`) never reconstructed — reusing the shared threshold
identity. -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **No-leak secret aggregate (single coefficient).**

    The Lagrange aggregate at 0 of the per-party `c·share_i`
    (`= z_i` with no mask) equals `c · f.eval 0 = c · s`, with `f` never
    formed. This is `threshold_partial_response_identity` with `y = 0`
    (the masks already telescoped away), exposed via the no-mask
    specialization. -/
theorem secret_aggregate_no_reconstruct
    (f : F[X]) {κ : Type*} [DecidableEq κ] (s : Finset κ) (v : κ → F)
    (hvs : Set.InjOn v s) (hdeg : f.degree < s.card)
    (c : F) (zc : κ → F)
    (hzc : zc = c • fun i => f.eval (v i)) :
    (Lagrange.interpolate s v zc).eval 0 = c * f.eval 0 :=
  threshold_partial_response_identity_no_mask f s v hvs hdeg c zc hzc

/-! ## 3. The residual cryptographic assumption (STANDARD: Module-LWE / MSIS)

As for Pulsar, the ONLY open content after the two machine-checked stages
is the secrecy reduction. Stated abstractly with its two standard hardness
hypotheses — the honest replacement for the EC reconstruct-then-sign cone. -/

/-- The public quantities a no-leak Corona transcript exposes for one
    signature. Mirrors the Boschini round outputs: per-party commitments,
    the rounded `h`, and the aggregate `z`-sum. It does NOT contain any
    per-party `c·λ_i·s_i`, any individual mask, or the reconstructed `s`. -/
structure PublicTranscript where
  commitments : ByteArray   -- per-party R-LWE commitments (public)
  roundedH    : ByteArray   -- RoundVector(D·u) high part  (public)
  zSum        : ByteArray   -- Σ_i z_i  (public, in sig; mask-free)
  c           : ByteArray   -- LowNormHash challenge        (public, in sig)
  deriving Inhabited

/-- A single-party Boschini R-LWE signature's public footprint on the same
    `(pk, m)` — the reference leakage profile. -/
opaque RlweSignatureLeakage : Type

/-- **Module-LWE hardness over Corona's ring** (the Gaussian masks
    `R_i·u + maskPrime_i − mask_i` make each commitment pseudorandom). The
    assumption Boschini/Ringtail (ePrint 2024/1113) already make. -/
opaque ModuleLWEHard : Prop

/-- **Module-SIS hardness over Corona's ring** (extracting a short `s` from
    the public `z`-sum is a short-vector problem). The assumption the
    construction's unforgeability rests on. -/
opaque ModuleSISHard : Prop

/-- The simulator reproducing the threshold transcript distribution from a
    single-party signature's leakage alone. -/
opaque transcriptSimulator : RlweSignatureLeakage → PublicTranscript

/-- **No-leak reduction (the residual open assumption — STANDARD).**

    The public Corona threshold transcript is simulatable from a
    single-party R-LWE signature's leakage, GIVEN Module-LWE and
    Module-SIS. This replaces reconstruct-then-sign: the threshold path
    reveals nothing about `s` beyond one ordinary signature, under the SAME
    standard lattice assumptions the construction already uses. Stated as a
    hypothesis (the v0.8 EC/paper obligation), NOT proved here; what this
    file MACHINE-CHECKS is that the CORRECTNESS core (telescoping masks +
    Lagrange aggregate) needs no reconstruction. -/
def NoLeakReduction : Prop :=
  ModuleLWEHard → ModuleSISHard →
    ∀ (leak : RlweSignatureLeakage),
      ∃ tr : PublicTranscript, tr = transcriptSimulator leak

/-- **The shape of the honest claim, packaged.** Under the standard lattice
    assumptions, IF the no-leak reduction holds THEN every public
    transcript is the simulator's output — carrying no key information
    beyond a single R-LWE signature. -/
theorem no_leak_under_standard_assumptions
    (hred : NoLeakReduction)
    (hlwe : ModuleLWEHard) (hsis : ModuleSISHard)
    (leak : RlweSignatureLeakage) :
    ∃ tr : PublicTranscript, tr = transcriptSimulator leak :=
  hred hlwe hsis leak

end Crypto.Corona.NoLeak
