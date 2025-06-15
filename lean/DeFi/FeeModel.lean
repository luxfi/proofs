/-
  DeFi Fee Model

  Maker-taker with volume tiers. Permissionless.
  No regulatory fee caps (pure DeFi).

  Maps to:
  - lux/exchange: fee calculation
  - lux/node: fee distribution to validators

  Properties:
  - Makers ≤ takers (incentivize liquidity)
  - Volume tiers: more volume → lower fees
  - Validator revenue: portion of fees to validators
  - Permissionless: fee schedule is on-chain and transparent

  Authors: Zach Kelling (Dec 2025), Woo Bin (Mar 2026)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace DeFi.FeeModel

/-- Fee tier -/
structure FeeTier where
  minVolume : Nat
  makerBps : Nat
  takerBps : Nat
  deriving DecidableEq, Repr

/-- Standard DeFi tiers -/
def tiers : List FeeTier :=
  [ ⟨0,        15, 30⟩       -- Tier 1
  , ⟨1000000,  10, 25⟩       -- Tier 2: $1M+
  , ⟨10000000,  5, 15⟩       -- Tier 3: $10M+
  , ⟨100000000, 0, 10⟩       -- Tier 4: $100M+ (zero maker)
  ]

/-- Calculate fee -/
def fee (tier : FeeTier) (isMaker : Bool) (value : Nat) : Nat :=
  value * (if isMaker then tier.makerBps else tier.takerBps) / 10000

/-- MAKER ≤ TAKER -/
theorem maker_le_taker (t : FeeTier) (v : Nat) (h : t.makerBps ≤ t.takerBps) :
    fee t true v ≤ fee t false v := by
  simp [fee]; exact Nat.div_le_div_right (Nat.mul_le_mul_left v h)

/-- TOP TIER ZERO MAKER -/
theorem top_tier_zero : (tiers[3]!).makerBps = 0 := by simp [tiers]

/-- VOLUME DISCOUNT -/
theorem volume_discount : (tiers[0]!).takerBps > (tiers[3]!).takerBps := by
  simp [tiers]

/-- 4 TIERS -/
theorem four_tiers : tiers.length = 4 := rfl

/-- VALIDATOR SHARE: Portion of fees goes to validators who process trades -/
def validatorShare (totalFee : Nat) (validatorPct : Nat) : Nat :=
  totalFee * validatorPct / 100

theorem validator_bounded (totalFee pct : Nat) (h : pct ≤ 100) :
    validatorShare totalFee pct ≤ totalFee := by
  simp [validatorShare]; exact Nat.div_le_of_le_mul (by omega)

end DeFi.FeeModel
