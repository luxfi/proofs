/-
  AI Compute Mint — No-Double-Mint & Per-Proof Supply Bound
  Models the spent-set discipline of the AI mining precompile: each verified
  work proof mints its reward AT MOST ONCE (replay prevention), and a single
  step never mints more than that proof's reward (no per-proof inflation).
  Maps to:
  - luxfi/precompile/ai/ai_mining.go : spentSet, IsSpent / MarkSpent, CalculateReward
  - HIP-0096 (anti-gaming / replay prevention), HIP-0001 ($AI supply)

  Self-contained: depends only on Lean 4 core (no Mathlib), so it compiles
  standalone without the Mathlib cache.
-/
namespace Compute.AIMint

abbrev WorkId := Nat
/-- The spent set as a decidable predicate (core Lean, no Finset/Mathlib). -/
abbrev Spent := WorkId → Bool

/-- One mint step. Idempotent on the spent set: an already-spent proof mints 0;
    a fresh proof mints `reward w` and is recorded as spent. -/
def mintStep (reward : WorkId → Nat) (spent : Spent) (w : WorkId) : Nat × Spent :=
  if spent w then (0, spent)
  else (reward w, fun x => spent x || x == w)

/-- No double-mint: a proof already in the spent set mints nothing. -/
theorem no_double_mint (reward : WorkId → Nat) (spent : Spent) (w : WorkId)
    (h : spent w = true) : (mintStep reward spent w).1 = 0 := by
  simp [mintStep, h]

/-- After processing a proof, it is spent (so it can never mint again). -/
theorem spent_after (reward : WorkId → Nat) (spent : Spent) (w : WorkId) :
    (mintStep reward spent w).2 w = true := by
  unfold mintStep
  by_cases h : spent w = true <;> simp [h]

/-- The spent set never shrinks: anything already spent stays spent. -/
theorem spent_monotone (reward : WorkId → Nat) (spent : Spent) (w x : WorkId)
    (hx : spent x = true) : (mintStep reward spent w).2 x = true := by
  unfold mintStep
  by_cases h : spent w = true <;> simp [h, hx]

/-- A step never mints more than the proof's reward (no per-proof inflation). -/
theorem mint_le_reward (reward : WorkId → Nat) (spent : Spent) (w : WorkId) :
    (mintStep reward spent w).1 ≤ reward w := by
  unfold mintStep
  by_cases h : spent w = true <;> simp [h]

end Compute.AIMint
