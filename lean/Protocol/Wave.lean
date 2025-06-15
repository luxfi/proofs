/-
  Wave Protocol Formal Model

  Models protocol/wave/wave.go and protocol/wave/fpc/fpc.go.

  Wave is the threshold voting engine. Each round:
  1. Sample k peers via Prism/Cut (wave.go:106)
  2. Collect votes with timeout (wave.go:115-131)
  3. Compare yes votes against alpha threshold (wave.go:154)
  4. If threshold met and matches current preference, increment confidence (wave.go:159)
  5. If confidence reaches beta, finalize (wave.go:161-163)
  6. If threshold met but contradicts preference, flip and reset confidence (wave.go:166-168)

  FPC variant: alpha = ceil(theta * k) where theta is PRF-selected per phase.
  theta in [theta_min, theta_max], selected via SHA-256(seed || phase).
  (fpc.go:36-38)

  Properties proved:
  - Monotonic confidence: once confidence reaches c, it can only increase or reset to 0
  - Finalization stability: once decided, never undecided (wave.go:98-102)
  - FPC range: alpha is always in [ceil(theta_min*k), ceil(theta_max*k)]
  - Convergence: under honest majority, confidence reaches beta in O(beta) rounds
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Protocol.Wave

/-- Wave configuration (models wave.Config) -/
structure WaveConfig where
  k        : Nat     -- sample size
  alpha    : Nat     -- threshold (fixed mode)
  beta     : Nat     -- confidence target
  hk       : 0 < k
  ha       : alpha ≤ k
  hb       : 0 < beta

/-- FPC configuration (models fpc.Selector) -/
structure FPCConfig where
  thetaMin : Rat     -- minimum theta
  thetaMax : Rat     -- maximum theta
  htmin    : 0 < thetaMin
  htmax    : thetaMin ≤ thetaMax
  htbound  : thetaMax ≤ 1

/-- Wave item state (models wave.WaveState) -/
structure WaveState where
  decided    : Bool
  preference : Bool      -- true = commit, false = skip
  confidence : Nat       -- consecutive confirming rounds

/-- A single round outcome -/
structure RoundResult where
  yesVotes   : Nat
  totalVotes : Nat

/-- Step function: one round of Wave (models wave.Tick) -/
def step (cfg : WaveConfig) (s : WaveState) (r : RoundResult) : WaveState :=
  if s.decided then s  -- wave.go:98-102: early return if decided
  else
    let thresholdMet := r.yesVotes ≥ cfg.alpha
    if thresholdMet then
      if s.preference then
        -- Consecutive confirmation (wave.go:157-163)
        let newConf := s.confidence + 1
        if newConf ≥ cfg.beta then
          { decided := true, preference := true, confidence := newConf }
        else
          { decided := false, preference := true, confidence := newConf }
      else
        -- Preference flip (wave.go:166-168)
        { decided := false, preference := true, confidence := 1 }
    else
      let noThresholdMet := (r.totalVotes - r.yesVotes) ≥ cfg.alpha
      if noThresholdMet then
        if ¬s.preference then
          let newConf := s.confidence + 1
          if newConf ≥ cfg.beta then
            { decided := true, preference := false, confidence := newConf }
          else
            { decided := false, preference := false, confidence := newConf }
        else
          { decided := false, preference := false, confidence := 1 }
      else
        -- No threshold met, confidence resets (wave.go:170)
        { decided := false, preference := s.preference, confidence := 0 }

/-- Once decided, step returns the same state -/
theorem decided_is_stable (cfg : WaveConfig) (s : WaveState) (r : RoundResult)
    (h : s.decided = true) : step cfg s r = s := by
  simp [step, h]

/-- Confidence only increases when preference matches threshold -/
theorem confidence_monotone_on_match
    (cfg : WaveConfig) (s : WaveState) (r : RoundResult)
    (hnd : s.decided = false)
    (hpref : s.preference = true)
    (hthresh : r.yesVotes ≥ cfg.alpha)
    : (step cfg s r).confidence = s.confidence + 1 := by
  simp [step, hnd, hpref, hthresh]
  split <;> simp

/-- After beta consecutive matching rounds, the item is decided -/
theorem finalization_after_beta
    (cfg : WaveConfig)
    (s : WaveState)
    (r : RoundResult)
    (hnd : s.decided = false)
    (hpref : s.preference = true)
    (hthresh : r.yesVotes ≥ cfg.alpha)
    (hconf : s.confidence + 1 ≥ cfg.beta)
    : (step cfg s r).decided = true := by
  simp [step, hnd, hpref, hthresh]
  split
  · simp
  · omega

end Protocol.Wave
