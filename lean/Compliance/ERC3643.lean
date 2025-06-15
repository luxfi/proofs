/-
  ERC-3643 Compliance Enforcement Correctness

  Formal model of the ERC-3643 (T-REX) canTransfer compliance gate.
  All security token transfers must pass six independent checks:
  whitelist membership, blacklist exclusion, lockup expiry, and
  jurisdiction compatibility. The compliance function is the conjunction.

  Maps to:
  - contracts/compliance/ERC3643Compliance.sol: canTransfer modifier
  - contracts/compliance/Whitelist.sol: investor registry
  - contracts/compliance/Lockup.sol: time-based transfer restrictions
  - contracts/compliance/Jurisdiction.sol: cross-border rules

  Properties:
  - Soundness: canTransfer = true implies all conditions hold
  - Completeness: all conditions holding implies canTransfer = true
  - Blacklist override: blacklisted users are always rejected
  - Lockup blocking: active lockup always blocks transfer
  - Decidability: canTransfer always terminates
-/

namespace Compliance.ERC3643

-- ═══════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════

/-- Address (opaque identifier for accounts) -/
abbrev Address := Nat

/-- Jurisdiction code (ISO 3166-1 numeric or internal enum) -/
abbrev Jurisdiction := Nat

/-- Timestamp (Unix epoch seconds) -/
abbrev Timestamp := Nat

/-- Investor registry: whitelist and blacklist membership,
    lockup expiry, and jurisdiction assignment. -/
structure Registry where
  isWhitelisted : Address → Bool
  isBlacklisted : Address → Bool
  lockupExpiry  : Address → Timestamp  -- 0 means no lockup
  jurisdiction  : Address → Jurisdiction

/-- Jurisdiction compatibility matrix.
    jurisdictionAllowed from to = true iff transfers between
    the two jurisdictions are permitted under applicable regulation. -/
structure JurisdictionPolicy where
  allowed : Jurisdiction → Jurisdiction → Bool

/-- Compliance context: registry + policy + current time -/
structure ComplianceCtx where
  registry : Registry
  policy   : JurisdictionPolicy
  now      : Timestamp

-- ═══════════════════════════════════════════════════════════════
-- COMPLIANCE PREDICATE
-- ═══════════════════════════════════════════════════════════════

/-- The six individual conditions for a compliant transfer -/
def fromWhitelisted (ctx : ComplianceCtx) (from_ : Address) : Bool :=
  ctx.registry.isWhitelisted from_

def toWhitelisted (ctx : ComplianceCtx) (to : Address) : Bool :=
  ctx.registry.isWhitelisted to

def fromNotBlacklisted (ctx : ComplianceCtx) (from_ : Address) : Bool :=
  !ctx.registry.isBlacklisted from_

def toNotBlacklisted (ctx : ComplianceCtx) (to : Address) : Bool :=
  !ctx.registry.isBlacklisted to

/-- Lockup has expired: either no lockup (expiry = 0) or now >= expiry -/
def lockupExpired (ctx : ComplianceCtx) (from_ : Address) : Bool :=
  ctx.registry.lockupExpiry from_ == 0 || ctx.now >= ctx.registry.lockupExpiry from_

def jurisdictionAllowed (ctx : ComplianceCtx) (from_ to : Address) : Bool :=
  ctx.policy.allowed (ctx.registry.jurisdiction from_) (ctx.registry.jurisdiction to)

/-- canTransfer: conjunction of all six conditions.
    This is the single compliance gate that every ERC-3643 transfer passes through. -/
def canTransfer (ctx : ComplianceCtx) (from_ to : Address) : Bool :=
  fromWhitelisted ctx from_ &&
  toWhitelisted ctx to &&
  fromNotBlacklisted ctx from_ &&
  toNotBlacklisted ctx to &&
  lockupExpired ctx from_ &&
  jurisdictionAllowed ctx from_ to

-- ═══════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════

/-- COMPLIANCE SOUNDNESS: If canTransfer returns true, every individual
    condition holds. This guarantees that no transfer slips through
    without satisfying the full compliance chain. -/
theorem compliance_sound
    (ctx : ComplianceCtx) (from_ to : Address)
    (h : canTransfer ctx from_ to = true) :
    fromWhitelisted ctx from_ = true ∧
    toWhitelisted ctx to = true ∧
    fromNotBlacklisted ctx from_ = true ∧
    toNotBlacklisted ctx to = true ∧
    lockupExpired ctx from_ = true ∧
    jurisdictionAllowed ctx from_ to = true := by
  simp [canTransfer] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- COMPLIANCE COMPLETENESS: If all six conditions hold individually,
    canTransfer returns true. Combined with soundness, this shows
    canTransfer is a faithful encoding of the compliance specification. -/
theorem compliance_complete
    (ctx : ComplianceCtx) (from_ to : Address)
    (h1 : fromWhitelisted ctx from_ = true)
    (h2 : toWhitelisted ctx to = true)
    (h3 : fromNotBlacklisted ctx from_ = true)
    (h4 : toNotBlacklisted ctx to = true)
    (h5 : lockupExpired ctx from_ = true)
    (h6 : jurisdictionAllowed ctx from_ to = true) :
    canTransfer ctx from_ to = true := by
  simp [canTransfer, h1, h2, h3, h4, h5, h6]

/-- BLACKLIST OVERRIDES WHITELIST: A blacklisted sender is always rejected,
    regardless of whitelist status. This models the real-world requirement
    that sanctions/freeze lists take absolute precedence. -/
theorem blacklist_overrides_whitelist
    (ctx : ComplianceCtx) (from_ to : Address)
    (h_bl : ctx.registry.isBlacklisted from_ = true) :
    canTransfer ctx from_ to = false := by
  simp [canTransfer, fromNotBlacklisted, h_bl]

/-- Blacklisted receiver is also always rejected -/
theorem blacklist_overrides_whitelist_receiver
    (ctx : ComplianceCtx) (from_ to : Address)
    (h_bl : ctx.registry.isBlacklisted to = true) :
    canTransfer ctx from_ to = false := by
  simp [canTransfer, fromWhitelisted, toWhitelisted, fromNotBlacklisted,
        toNotBlacklisted, lockupExpired, jurisdictionAllowed, h_bl]

/-- LOCKUP BLOCKS TRANSFER: An active lockup (expiry > 0 and now < expiry)
    blocks the transfer even if the sender is whitelisted and not blacklisted.
    This enforces holding periods for regulatory compliance (e.g., Reg D). -/
theorem lockup_blocks_transfer
    (ctx : ComplianceCtx) (from_ to : Address)
    (h_expiry_set : ctx.registry.lockupExpiry from_ ≠ 0)
    (h_active : ctx.now < ctx.registry.lockupExpiry from_) :
    canTransfer ctx from_ to = false := by
  have h_not_expired : lockupExpired ctx from_ = false := by
    unfold lockupExpired
    simp only [beq_false_of_ne h_expiry_set, Bool.false_or]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    exact h_active
  simp [canTransfer, h_not_expired]

/-- COMPLIANCE IS DECIDABLE: canTransfer always terminates with true or false.
    This is structurally guaranteed because canTransfer is a total Boolean
    function — no recursion, no partiality, no Option. -/
theorem compliance_is_decidable
    (ctx : ComplianceCtx) (from_ to : Address) :
    canTransfer ctx from_ to = true ∨ canTransfer ctx from_ to = false := by
  cases h : canTransfer ctx from_ to
  · right; rfl
  · left; rfl

/-- Non-whitelisted sender is rejected -/
theorem non_whitelisted_sender_rejected
    (ctx : ComplianceCtx) (from_ to : Address)
    (h : ctx.registry.isWhitelisted from_ = false) :
    canTransfer ctx from_ to = false := by
  simp [canTransfer, fromWhitelisted, h]

/-- Non-whitelisted receiver is rejected -/
theorem non_whitelisted_receiver_rejected
    (ctx : ComplianceCtx) (from_ to : Address)
    (h : ctx.registry.isWhitelisted to = false) :
    canTransfer ctx from_ to = false := by
  simp [canTransfer, fromWhitelisted, toWhitelisted, fromNotBlacklisted,
        toNotBlacklisted, lockupExpired, jurisdictionAllowed, h]

/-- Jurisdiction mismatch rejects transfer -/
theorem jurisdiction_mismatch_rejected
    (ctx : ComplianceCtx) (from_ to : Address)
    (h : ctx.policy.allowed (ctx.registry.jurisdiction from_)
                            (ctx.registry.jurisdiction to) = false) :
    canTransfer ctx from_ to = false := by
  simp [canTransfer, fromWhitelisted, toWhitelisted, fromNotBlacklisted,
        toNotBlacklisted, lockupExpired, jurisdictionAllowed, h]

end Compliance.ERC3643
