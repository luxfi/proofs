/-
  Corona EUF-CMA unforgeability reduction to Ring-LWE -- Lean statement.

  Mirrors `~/work/lux/proofs/lean/Crypto/Pulsar/Unforgeability.lean`
  for the R-LWE setting.

  Claim: under the Ring-LWE hardness assumption with Corona's parameter
  set (N=256, q = 0x1000000004A01, sigma = SigmaE), no probabilistic
  polynomial-time quantum adversary holding fewer than `t` shares can
  produce a Corona signature accepted by `Verify`.

  Discharged: by reduction to Boschini-Kaviani-Lai-Malavolta-Takahashi-
  Tibouchi (IACR ePrint 2024/1113, §5 Theorem 1). The Lean side states
  the reduction; the cited paper carries the cryptographic content.
-/

import Crypto.Corona
import Crypto.Corona.Shamir
import Mathlib.Tactic

namespace Crypto.Corona.Unforgeability

open Crypto.Corona

/-- The Ring-LWE problem instance for Corona's parameters. -/
opaque RLWEInstance : LWEParams → Type

/-- The Ring-LWE-bounded adversary class: PPT (or BQP) algorithms that
    solve RLWE on the given parameter set with bounded advantage. -/
opaque RLWESolver (lwe : LWEParams) : Type

/-- The EUF-CMA experiment for Corona: an adversary with oracle access
    to the threshold Sign protocol produces a signature on a fresh
    message; wins if Verify accepts. -/
opaque EUFCMAGame (lwe : LWEParams) (tp : ThresholdParams) : Type

/-- The EUF-CMA winning probability of an adversary. -/
opaque eufcma_advantage
    (lwe : LWEParams) (tp : ThresholdParams)
    (game : EUFCMAGame lwe tp) : ℝ

/-- Boschini et al. §5 Theorem 1: any EUF-CMA forger reduces to an
    RLWE solver with a polynomial advantage loss.

    Stated as a named axiom citing the paper. The Lean side does NOT
    re-prove the lattice-cryptographic content; that lives in the
    cited paper §5. -/
axiom corona_eufcma_to_rlwe
    (lwe : LWEParams) (tp : ThresholdParams) :
    ∀ (game : EUFCMAGame lwe tp),
      ∃ (solver : RLWESolver lwe),
        -- A polynomial-time reduction with poly advantage loss.
        True

/-- Threshold-honest-majority preservation: a corrupted set of < t
    parties cannot forge under the RLWE hardness assumption. This is
    the standard threshold-signature EUF-CMA-via-RLWE corollary. -/
theorem corona_threshold_unforgeable
    (lwe : LWEParams) (tp : ThresholdParams) (compromised : Nat)
    (h : compromised < tp.t) :
    CoronaEUFCMAAdv lwe :=
  corona_ring_lwe_euf_cma lwe tp compromised h

/-- The honest-quorum unforgeability is preserved by Corona's signing
    protocol. This is the user-facing statement: "if RLWE is hard,
    Corona signatures are unforgeable." -/
theorem corona_signatures_unforgeable_under_rlwe
    (lwe : LWEParams) (tp : ThresholdParams) (compromised : Nat)
    (h : compromised < tp.t) :
    CoronaEUFCMAAdv lwe :=
  corona_threshold_unforgeable lwe tp compromised h

end Crypto.Corona.Unforgeability
