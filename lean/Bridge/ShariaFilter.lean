/-
  ShariaFilter Formal Properties

  On-chain Shariah compliance filter for the YieldVault strategy set.
  A ShariahBoard (single address, transferable only by itself) classifies
  strategies as HALAL, HARAM, or PENDING. Only HALAL strategies are
  eligible for vault deployment.

  Maps to:
  - contracts/bridge/ShariaFilter.sol: compliance classification
  - contracts/bridge/YieldVault.sol: filterCompliant gate

  Properties:
  - SAB sovereignty (only shariahBoard can modify shariahBoard)
  - Classification completeness (every strategy has exactly one status)
  - Halal filter soundness (filterCompliant returns only HALAL)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Bridge.ShariaFilter

-- ═══════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════

/-- Address (models Solidity address) -/
abbrev Address := Nat

/-- Compliance classification -/
inductive ComplianceStatus where
  | halal   : ComplianceStatus
  | haram   : ComplianceStatus
  | pending : ComplianceStatus
  deriving DecidableEq, Repr

/-- Strategy with compliance status -/
structure Strategy where
  addr : Address
  status : ComplianceStatus
  deriving DecidableEq, Repr

/-- Filter state -/
structure FilterState where
  shariahBoard : Address
  strategies : List Strategy
  deriving Repr

-- ═══════════════════════════════════════════════════════════════
-- CORE FUNCTIONS
-- ═══════════════════════════════════════════════════════════════

/-- Transfer the shariahBoard role. Only callable by current board. -/
def transferBoard (st : FilterState) (caller newBoard : Address) :
    Option FilterState :=
  if caller = st.shariahBoard then
    some { st with shariahBoard := newBoard }
  else none

/-- Classify a strategy. Only callable by shariahBoard. -/
def classify (st : FilterState) (caller : Address)
    (stratAddr : Address) (status : ComplianceStatus) :
    Option FilterState :=
  if caller = st.shariahBoard then
    some { st with strategies :=
      st.strategies.map fun s =>
        if s.addr = stratAddr then { s with status := status } else s }
  else none

/-- Filter: return only HALAL strategies -/
def filterCompliant (st : FilterState) : List Strategy :=
  st.strategies.filter fun s => s.status = ComplianceStatus.halal

/-- Lookup a strategy's status -/
def getStatus (st : FilterState) (addr : Address) : Option ComplianceStatus :=
  (st.strategies.find? fun s => s.addr = addr).map Strategy.status

-- ═══════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════

/-- SAB SOVEREIGNTY: Only the current shariahBoard address can modify
    the shariahBoard address. No other address can transfer the role. -/
theorem sab_sovereignty (st : FilterState) (caller newBoard : Address)
    (h : caller ≠ st.shariahBoard) :
    transferBoard st caller newBoard = none := by
  simp [transferBoard, h]

/-- Board transfer succeeds when caller is the board -/
theorem sab_transfer_authorized (st : FilterState) (newBoard : Address) :
    ∃ st', transferBoard st st.shariahBoard newBoard = some st' ∧
      st'.shariahBoard = newBoard := by
  exact ⟨{ st with shariahBoard := newBoard },
    by simp [transferBoard], by rfl⟩

/-- Board address preserved when caller unauthorized -/
theorem sab_unchanged_on_reject (st : FilterState) (caller newBoard : Address)
    (h : caller ≠ st.shariahBoard) :
    transferBoard st caller newBoard = none := by
  simp [transferBoard, h]

/-- Classification requires board authority -/
theorem classify_requires_board (st : FilterState) (caller stratAddr : Address)
    (status : ComplianceStatus) (h : caller ≠ st.shariahBoard) :
    classify st caller stratAddr status = none := by
  simp [classify, h]

/-- CLASSIFICATION COMPLETENESS: Every strategy in the list has exactly
    one ComplianceStatus by construction (it's a field of the struct).
    There is no "unclassified" state — default is `pending`. -/
theorem classification_completeness (st : FilterState) :
    ∀ s ∈ st.strategies,
      s.status = ComplianceStatus.halal ∨
      s.status = ComplianceStatus.haram ∨
      s.status = ComplianceStatus.pending := by
  intro s _
  cases s.status with
  | halal => left; rfl
  | haram => right; left; rfl
  | pending => right; right; rfl

/-- Each strategy has exactly one status (not two simultaneously) -/
theorem classification_exclusive (s : Strategy)
    (h1 : s.status = ComplianceStatus.halal)
    (h2 : s.status = ComplianceStatus.haram) :
    False := by
  rw [h1] at h2; exact ComplianceStatus.noConfusion h2

/-- HALAL FILTER SOUNDNESS: filterCompliant returns only strategies
    with status = HALAL. No HARAM or PENDING strategy leaks through. -/
theorem halal_filter_soundness (st : FilterState) :
    ∀ s ∈ filterCompliant st, s.status = ComplianceStatus.halal := by
  intro s hs
  simp [filterCompliant, List.mem_filter] at hs
  exact hs.2

/-- Converse: every HALAL strategy in the list is in the filtered output -/
theorem halal_filter_completeness (st : FilterState) (s : Strategy)
    (h_mem : s ∈ st.strategies) (h_halal : s.status = ComplianceStatus.halal) :
    s ∈ filterCompliant st := by
  simp [filterCompliant, List.mem_filter]
  exact ⟨h_mem, h_halal⟩

/-- HARAM strategies are excluded -/
theorem haram_excluded (st : FilterState) (s : Strategy)
    (h : s.status = ComplianceStatus.haram) :
    s ∉ filterCompliant st := by
  simp [filterCompliant, List.mem_filter]
  intro _
  rw [h]
  exact ComplianceStatus.noConfusion

/-- PENDING strategies are excluded -/
theorem pending_excluded (st : FilterState) (s : Strategy)
    (h : s.status = ComplianceStatus.pending) :
    s ∉ filterCompliant st := by
  simp [filterCompliant, List.mem_filter]
  intro _
  rw [h]
  exact ComplianceStatus.noConfusion

end Bridge.ShariaFilter
