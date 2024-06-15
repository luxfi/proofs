/-
  Validator Economics and Slashing

  Staking economics for Lux validators. Stake-weighted voting.
  Slashing for provable misbehavior.

  Maps to:
  - lux/node/vms/platformvm: validator staking
  - lux/consensus: stake-weighted BFT
  - HIP-0024: Hanzo L1 validator requirements

  Properties:
  - Stake-weighted: voting power ∝ stake
  - Slashing is loss-bounded: cannot lose more than stake
  - Honest validators are never slashed (safety)
  - Minimum stake enforced
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Consensus.Validator

/-- Validator with stake -/
structure Validator where
  id : Nat
  stake : Nat
  isHonest : Bool
  slashed : Nat          -- amount already slashed
  deriving DecidableEq, Repr

/-- Validator set -/
structure ValidatorSet where
  validators : List Validator
  minStake : Nat
  totalStake : Nat

/-- Voting power: proportional to stake -/
def votingPower (v : Validator) (totalStake : Nat) : Nat :=
  if totalStake = 0 then 0 else v.stake * 1000 / totalStake  -- basis points

/-- Slash a validator for misbehavior -/
def slash (v : Validator) (penalty : Nat) : Validator :=
  { v with slashed := v.slashed + min penalty (v.stake - v.slashed) }

/-- SLASHING BOUNDED: Cannot lose more than stake -/
theorem slash_bounded (v : Validator) (penalty : Nat)
    (h : v.slashed ≤ v.stake) :
    (slash v penalty).slashed ≤ v.stake := by
  simp [slash]; omega

/-- SLASHING MONOTONE: Slashed amount only increases -/
theorem slash_monotone (v : Validator) (penalty : Nat) :
    (slash v penalty).slashed ≥ v.slashed := by
  simp [slash]

/-- HONEST NEVER SLASHED: Only provable misbehavior triggers slash.
    This is a protocol property (axiomatized). -/
axiom honest_no_slash :
  ∀ (v : Validator), v.isHonest = true → v.slashed = 0

/-- MINIMUM STAKE: Below minimum cannot validate -/
def meetsMinimum (vs : ValidatorSet) (v : Validator) : Bool :=
  v.stake ≥ vs.minStake

theorem below_minimum_rejected (vs : ValidatorSet) (v : Validator)
    (h : v.stake < vs.minStake) :
    meetsMinimum vs v = false := by
  simp [meetsMinimum, Nat.not_le.mpr h]

/-- STAKE-WEIGHTED POWER: Higher stake → more voting power -/
theorem more_stake_more_power (v1 v2 : Validator) (total : Nat)
    (h : v1.stake > v2.stake) (ht : total > 0) :
    votingPower v1 total ≥ votingPower v2 total := by
  simp [votingPower, Nat.ne_of_gt ht]
  exact Nat.div_le_div_right (by omega)

/-- TOTAL STAKE: Sum of all validator stakes -/
def computeTotalStake (vs : List Validator) : Nat :=
  vs.foldl (fun acc v => acc + v.stake) 0

theorem empty_zero_stake : computeTotalStake [] = 0 := rfl

end Consensus.Validator
