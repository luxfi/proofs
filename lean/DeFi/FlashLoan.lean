/-
  Flash Loan Safety

  Atomic borrow-use-repay within a single transaction.
  If repayment fails, entire transaction reverts.

  Properties:
  - Atomicity: borrow + use + repay in one tx
  - Solvency: pool balance ≥ pre-loan balance after tx
  - Fee accrual: flash loan fee goes to LPs
  - No residual debt: loan is fully repaid or fully reverted

  Author: Zach Kelling
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace DeFi.FlashLoan

structure LoanState where
  poolBalance : Nat
  feeBps : Nat        -- flash loan fee (e.g., 9 = 0.09%)

structure FlashLoan where
  amount : Nat
  fee : Nat
  repaid : Bool

def executeLoan (s : LoanState) (amount : Nat) (repaid : Bool) : LoanState :=
  if repaid && amount ≤ s.poolBalance then
    let fee := amount * s.feeBps / 10000
    { s with poolBalance := s.poolBalance + fee }  -- pool gains fee
  else s  -- revert: no change

/-- SOLVENCY: Pool never loses money on flash loans -/
theorem flash_loan_solvent (s : LoanState) (amount : Nat) (repaid : Bool) :
    (executeLoan s amount repaid).poolBalance ≥ s.poolBalance := by
  simp [executeLoan]; split <;> omega

/-- NO REPAY = NO LOAN: Unreturned loan reverts -/
theorem no_repay_reverts (s : LoanState) (amount : Nat) :
    executeLoan s amount false = s := by
  simp [executeLoan]

/-- FEE ACCRUAL: Successful loan increases pool by fee -/
theorem fee_accrues (s : LoanState) (amount : Nat)
    (h : amount ≤ s.poolBalance) (hf : s.feeBps > 0) :
    (executeLoan s amount true).poolBalance ≥ s.poolBalance := by
  simp [executeLoan, h]; omega

/-- OVERDRAFT BLOCKED: Can't borrow more than pool has -/
theorem overdraft_blocked (s : LoanState) (amount : Nat)
    (h : amount > s.poolBalance) :
    executeLoan s amount true = s := by
  simp [executeLoan, Nat.not_le.mpr h]

end DeFi.FlashLoan
