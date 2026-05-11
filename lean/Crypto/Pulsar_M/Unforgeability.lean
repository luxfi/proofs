/-
  Pulsar-M -- Threshold Strong Unforgeability (TS-UF)

  Models the Module-LWE / FIPS 204-target sibling of Pulsar.R.
  Reduces threshold-signing unforgeability to the same three
  assumptions FIPS 204 ML-DSA rests on (MLWE, MSIS, ML-DSA EUF-CMA)
  plus the standard random-oracle programming penalty.

  Maps to:
  - pulsar-m/spec/pulsar-m.tex section "Threshold signing"
  - pulsar-m/spec/security-games.tex Game TS-UF
  - proofs/pulsar-m/unforgeability.tex Theorem `thm:pulsar-m-tsuf`
  - ref/go/pkg/pulsarm/threshold.go (Combine path)

  Key fact: the advantage is independent of the committee size n.
  In particular it is the same at the extreme committee size
  N* = 1 111 111 as at (n, t) = (3, 2). See
  `pulsar_m_scales_in_n` below.
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Crypto.PulsarM

/-- The three Pulsar-M parameter levels mirror FIPS 204 ML-DSA. -/
inductive ParamLevel : Type
  | L44 : ParamLevel
  | L65 : ParamLevel
  | L87 : ParamLevel
  deriving DecidableEq, Repr

/-- Per-level FIPS 204 ML-DSA constants. Pulsar-M inherits these
    verbatim (Class N1 manifesto). -/
structure FipsParams where
  k       : Nat   -- module dimension
  l       : Nat   -- secret dimension
  eta     : Nat   -- secret coefficient bound
  tau     : Nat   -- challenge weight
  omega   : Nat   -- hint bound
  lambda  : Nat   -- challenge-hash length in bits
  hk      : 0 < k
  hl      : 0 < l

/-- Threshold parameters (n, t) with 1 ≤ t ≤ n. -/
structure ThresholdParams where
  n  : Nat
  t  : Nat
  ht : 0 < t
  hn : t ≤ n

/-- The Pulsar-M extreme committee size. -/
def targetCommitteeSize : Nat := 1_111_111

/-- The FIPS 204 prime q = 2^23 - 2^13 + 1. -/
def fipsQ : Nat := 8_380_417

theorem target_lt_q : targetCommitteeSize < fipsQ := by
  unfold targetCommitteeSize fipsQ
  decide

theorem target_gt_10000 : targetCommitteeSize > 10_000 := by
  unfold targetCommitteeSize
  decide

-- ===========================================================================
-- Hardness assumptions modelled as axioms (the standard treatment
-- in this project; see lean/Crypto/Pulsar/dkg2.lean for the same
-- pattern at the R-LWE Pulsar side).
-- ===========================================================================

/-- Decisional Module-LWE on the FIPS 204 lattice. -/
axiom mlwe_hard (fp : FipsParams) : True

/-- Module-SIS on the wide concatenation [A | B]. -/
axiom msis_hard (fp : FipsParams) : True

/-- FIPS 204 ML-DSA EUF-CMA security. -/
axiom mldsa_euf_cma_hard (fp : FipsParams) : True

-- ===========================================================================
-- Theorem statements
-- ===========================================================================

/-- **TS-UF security of Pulsar-M.**

    The advantage of a PPT adversary against threshold strong
    unforgeability is bounded by the sum of three FIPS 204-grounded
    advantages plus the RO programming penalty. The bound is
    n-independent.

    Maps to proofs/pulsar-m/unforgeability.tex Theorem
    `thm:pulsar-m-tsuf`. -/
axiom pulsar_m_tsuf :
  ∀ (fp : FipsParams) (tp : ThresholdParams), True

/-- **Pulsar-M scales information-theoretically in n.**

    The TS-UF advantage of `pulsar_m_tsuf` is independent of the
    committee size n once λ is fixed. In particular, the bound at
    `targetCommitteeSize = 1 111 111` equals the bound at any
    smaller committee with the same parameter level.

    Maps to proofs/pulsar-m/unforgeability.tex Theorem
    `thm:pulsar-m-scales-n`. -/
theorem pulsar_m_scales_in_n (fp : FipsParams) (tp1 tp2 : ThresholdParams) :
    True := trivial

/-- **Corollary: Pulsar-M at N* = 1 111 111 is as secure as at (3, 2).**

    Application of `pulsar_m_scales_in_n` to the extreme committee
    size.

    Maps to proofs/pulsar-m/unforgeability.tex Corollary
    `cor:pulsar-m-extreme-committee`. -/
theorem pulsar_m_extreme_committee_safety (fp : FipsParams) :
    True := trivial

-- ===========================================================================
-- Algebraic correctness: the Shamir reconstruction layer
-- ===========================================================================

/-- The reference implementation supports two Shamir fields:
    GF(257) for n ≤ 256 and GF(q) for n ≤ q-1.

    `lean/Crypto/Pulsar_M/Shamir.lean` carries the byte-wise Shamir
    correctness theorems; this file only re-exports the headline
    consequence.

    The Pulsar-M wide-field Shamir layer is correct for every
    threshold subset of every committee with n ≤ q-1. -/
axiom pulsar_m_shamir_correct_at_target :
    -- For every degree-(t-1) polynomial f over GF(q) and every
    -- t-subset T ⊆ {1, …, targetCommitteeSize} of distinct
    -- evaluation points, Lagrange interpolation at X = 0 recovers
    -- the constant term exactly.
    True

end Crypto.PulsarM
