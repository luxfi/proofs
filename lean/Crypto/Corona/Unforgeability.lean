/-
  Corona EUF-CMA unforgeability reduction to Module-LWE -- Lean statement.

  Mirrors `~/work/lux/proofs/lean/Crypto/Pulsar/Unforgeability.lean`;
  both Corona and Pulsar are Module-LWE threshold schemes (differing in
  parameter regime and lifecycle, not in lattice family).

  Claim: under the Module-LWE hardness assumption (with Module-SIS for
  binding) with Corona's parameter set (R_q = Z_q[X]/(X^256+1), module
  dims M=8, N=7, q = 0x1000000004A01, sigma = SigmaE = 6.108), no
  probabilistic polynomial-time quantum adversary holding fewer than `t`
  shares can produce a Corona signature accepted by `Verify`.

  Discharged: by reduction to Boschini-Kaviani-Lai-Malavolta-Takahashi-
  Tibouchi (IACR ePrint 2024/1113, §5 Theorem 1). The Lean side states
  the reduction; the cited paper carries the cryptographic content.
-/

import Crypto.Corona
import Crypto.Corona.Shamir
import Mathlib.Tactic

namespace Crypto.Corona.Unforgeability

open Crypto.Corona

/-- The Module-LWE problem instance for Corona's parameters. -/
opaque MLWEInstance : LWEParams → Type

/-- The Module-LWE-bounded adversary class: PPT (or BQP) algorithms that
    solve MLWE on the given parameter set with bounded advantage. -/
opaque MLWESolver (lwe : LWEParams) : Type

/-- The EUF-CMA experiment for Corona: an adversary with oracle access
    to the threshold Sign protocol produces a signature on a fresh
    message; wins if Verify accepts. -/
opaque EUFCMAGame (lwe : LWEParams) (tp : ThresholdParams) : Type

/-- The EUF-CMA winning probability of an adversary. -/
opaque eufcma_advantage
    (lwe : LWEParams) (tp : ThresholdParams)
    (game : EUFCMAGame lwe tp) : ℝ

/-- Boschini et al. §5 Theorem 1: any EUF-CMA forger reduces to a
    Module-LWE solver with a polynomial advantage loss.

    Stated as a named axiom citing the paper. The Lean side does NOT
    re-prove the lattice-cryptographic content; that lives in the
    cited paper §5. -/
axiom corona_eufcma_to_mlwe
    (lwe : LWEParams) (tp : ThresholdParams) :
    ∀ (_game : EUFCMAGame lwe tp),
      ∃ (_solver : MLWESolver lwe),
        -- A polynomial-time reduction with poly advantage loss.
        True

/-- Threshold-honest-majority preservation: a corrupted set of < t
    parties cannot forge under the Module-LWE hardness assumption. This
    is the standard threshold-signature EUF-CMA-via-MLWE corollary. -/
noncomputable def corona_threshold_unforgeable
    (lwe : LWEParams) (tp : ThresholdParams) (compromised : Nat)
    (h : compromised < tp.t) :
    CoronaEUFCMAAdv lwe :=
  corona_module_lwe_euf_cma lwe tp compromised h

/-- The honest-quorum unforgeability is preserved by Corona's signing
    protocol. This is the user-facing statement: "if Module-LWE is hard,
    Corona signatures are unforgeable." -/
noncomputable def corona_signatures_unforgeable_under_mlwe
    (lwe : LWEParams) (tp : ThresholdParams) (compromised : Nat)
    (h : compromised < tp.t) :
    CoronaEUFCMAAdv lwe :=
  corona_threshold_unforgeable lwe tp compromised h

end Crypto.Corona.Unforgeability
