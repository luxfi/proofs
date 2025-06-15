/-
  Coeffect Algebra

  Effects: what a computation DOES to the world.
  Coeffects: what a computation NEEDS from the world.

  A pure build needs nothing external (coeffects = ∅).
  An impure build needs time, random, network, filesystem, etc.
  The tensor product (⊗ = append) combines coeffects.

  Maps to:
  - hanzo/runtime: sandbox coeffect tracking
  - hanzo/attest: discharge proof generation
  - lux/node: build reproducibility checking

  Properties:
  - Pure is identity for tensor
  - Tensor is associative
  - Pure ⊗ pure = pure
  - Time and random are non-reproducible
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Build.Coeffect

/-- What a build needs from the world -/
inductive Coeffect where
  | pure                         -- Needs nothing
  | filesystem (path : String)   -- Non-CA file access
  | filesystemCA (hash : Nat)   -- Content-addressed file
  | network (host : String)      -- Non-CA network
  | networkCA (hash : Nat)      -- Content-addressed network
  | time                         -- Wall clock (non-reproducible)
  | random                       -- Entropy (non-reproducible)
  | gpu (device : String)       -- GPU access (non-deterministic)
  | auth (provider : String)    -- Credential access (ephemeral)
  | tee (attestation : Nat)     -- TEE hardware attestation
  deriving DecidableEq, Repr

/-- A coeffect set (tensor = append) -/
abbrev Coeffects := List Coeffect

/-- Pure coeffect set (empty = needs nothing) -/
def Coeffects.pure : Coeffects := []

/-- Check if coeffects are pure -/
def Coeffects.isPure (r : Coeffects) : Bool := r.isEmpty

/-- Check if coeffects allow reproducible builds -/
def Coeffects.isReproducible (r : Coeffects) : Bool :=
  r.all fun c => match c with
    | .pure | .filesystemCA _ | .networkCA _ | .tee _ => true
    | .time | .random | .gpu _ | .auth _ => false
    | .filesystem _ | .network _ => false

-- ═══════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════

/-- Empty coeffects are pure -/
theorem empty_is_pure : Coeffects.isPure [] = true := rfl

/-- Pure coeffects are reproducible -/
theorem pure_is_reproducible : Coeffects.isReproducible [] = true := rfl

/-- Tensor with pure is identity (right) -/
theorem tensor_pure_right (r : Coeffects) : r ++ [] = r :=
  List.append_nil r

/-- Tensor with pure is identity (left) -/
theorem tensor_pure_left (r : Coeffects) : [] ++ r = r := rfl

/-- Tensor is associative -/
theorem tensor_assoc (a b c : Coeffects) : (a ++ b) ++ c = a ++ (b ++ c) :=
  List.append_assoc a b c

/-- Pure ⊗ pure = pure -/
theorem tensor_pure_pure (a b : Coeffects)
    (ha : a.isPure) (hb : b.isPure) : (a ++ b).isPure := by
  simp [Coeffects.isPure, List.isEmpty_iff] at *
  simp [ha, hb]

/-- Reproducible ⊗ reproducible = reproducible -/
theorem tensor_reproducible (a b : Coeffects)
    (ha : a.isReproducible) (hb : b.isReproducible) :
    (a ++ b).isReproducible := by
  simp [Coeffects.isReproducible, List.all_append, Bool.and_eq_true]
  exact ⟨ha, hb⟩

/-- Time is not reproducible -/
theorem time_not_reproducible :
    Coeffects.isReproducible [.time] = false := rfl

/-- Random is not reproducible -/
theorem random_not_reproducible :
    Coeffects.isReproducible [.random] = false := rfl

/-- GPU is not reproducible -/
theorem gpu_not_reproducible (d : String) :
    Coeffects.isReproducible [.gpu d] = false := rfl

/-- Auth is not reproducible -/
theorem auth_not_reproducible (p : String) :
    Coeffects.isReproducible [.auth p] = false := rfl

/-- Content-addressed filesystem IS reproducible -/
theorem ca_filesystem_reproducible (h : Nat) :
    Coeffects.isReproducible [.filesystemCA h] = true := rfl

/-- TEE attestation IS reproducible -/
theorem tee_reproducible (a : Nat) :
    Coeffects.isReproducible [.tee a] = true := rfl

end Build.Coeffect
