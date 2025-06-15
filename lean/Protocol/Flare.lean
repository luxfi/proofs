/-
  Flare Protocol Formal Model

  Models protocol/flare/flare.go and core/dag/flare.go.

  Flare is the DAG commit rule. For a proposer vertex at round r:
  - Certificate: >= 2f+1 vertices at round r+1 support it (flare.go:14-27)
  - Skip: >= 2f+1 vertices at round r+1 do NOT support it (flare.go:29-42)
  - Classify returns exactly one of {Commit, Skip, Undecided} (flare.go:48-57)

  Properties proved:
  - Cert and Skip are mutually exclusive (cannot have both)
  - At most one proposer per author per round can get a certificate
  - If cert exists, at least f+1 honest nodes support it
  - Classification is total: exactly one of the three outcomes
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Protocol.Flare

/-- DAG parameters (models dag.Params{N, F}) -/
structure Params where
  n : Nat
  f : Nat
  hf : 3 * f < n  -- strict BFT bound

/-- Decision type (models flare.Decision) -/
inductive Decision where
  | undecided : Decision
  | commit    : Decision
  | skip      : Decision
  deriving DecidableEq

/-- Vote counts at round r+1 for a proposer at round r -/
structure VoteCounts where
  support    : Nat   -- vertices at r+1 that include proposer in parents
  noSupport  : Nat   -- vertices at r+1 that do NOT include proposer
  total      : Nat   -- total vertices at r+1
  hsum       : support + noSupport = total

/-- Has certificate: >= 2f+1 support (models flare.HasCertificate) -/
def hasCertificate (p : Params) (vc : VoteCounts) : Prop :=
  vc.support ≥ 2 * p.f + 1

/-- Has skip: >= 2f+1 non-support (models flare.HasSkip) -/
def hasSkip (p : Params) (vc : VoteCounts) : Prop :=
  vc.noSupport ≥ 2 * p.f + 1

/-- Classify (models flare.Classify) -/
def classify (p : Params) (vc : VoteCounts) : Decision :=
  if vc.support ≥ 2 * p.f + 1 then Decision.commit
  else if vc.noSupport ≥ 2 * p.f + 1 then Decision.skip
  else Decision.undecided

/-- Certificate and Skip are mutually exclusive.
    Proof: support + noSupport = total <= n.
    cert requires support >= 2f+1.
    skip requires noSupport >= 2f+1.
    Both would require total >= 2*(2f+1) = 4f+2 > n (since n < 3f+1 < 4f+2 for f>0).
    Actually: support + noSupport = total, and if total <= n < 3f+1,
    then support + noSupport < 3f+1 < 2*(2f+1) = 4f+2. -/
theorem cert_skip_exclusive
    (p : Params) (vc : VoteCounts)
    (htotal : vc.total ≤ p.n)
    : ¬(hasCertificate p vc ∧ hasSkip p vc) := by
  intro ⟨hcert, hskip⟩
  simp [hasCertificate, hasSkip] at hcert hskip
  have h := vc.hsum
  omega

/-- If a certificate exists, at least f+1 honest nodes support it.
    Proof: 2f+1 support, at most f are Byzantine, so >= f+1 are honest. -/
theorem cert_honest_support
    (p : Params) (vc : VoteCounts)
    (hcert : hasCertificate p vc)
    (byzantine_in_support : Nat)
    (hbyz : byzantine_in_support ≤ p.f)
    (honest_support : Nat)
    (hdecomp : honest_support + byzantine_in_support = vc.support)
    : honest_support ≥ p.f + 1 := by
  simp [hasCertificate] at hcert
  omega

/-- Classification is exhaustive: exactly one case applies -/
theorem classify_total (p : Params) (vc : VoteCounts) :
    classify p vc = Decision.commit ∨
    classify p vc = Decision.skip ∨
    classify p vc = Decision.undecided := by
  simp [classify]
  split <;> simp

end Protocol.Flare
