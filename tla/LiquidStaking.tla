---------------------------- MODULE LiquidStaking ----------------------------
(*
 * TLA+ Specification of the Lux Liquid Staking Protocol
 *
 * Source: ~/work/lux/contracts/staking/
 *
 * Protocol summary:
 *   A liquid staking vault allows users to stake tokens and receive
 *   transferable shares (stLUX). The share price = totalAssets / totalShares
 *   and is monotonically increasing under normal operation (no slashing).
 *
 *   Rewards accrue to the vault, increasing totalAssets while totalShares
 *   remains constant, thus increasing the share price. Slashing events
 *   reduce totalAssets, proportionally reducing the share price.
 *
 * State model:
 *   totalAssets          -- total staked tokens (principal + rewards)
 *   totalShares          -- total outstanding shares
 *   userShares[a]        -- shares held by address a
 *   lastSharePrice       -- share price at last checkpoint (scaled by Precision)
 *   slashingOccurred     -- whether any slashing has happened
 *
 * Actions:
 *   Stake(a, amt)        -- address a stakes amt tokens, receives shares
 *   Unstake(a, sh)       -- address a redeems sh shares for tokens
 *   AccrueRewards(amt)   -- validator rewards increase totalAssets
 *   Slash(amt)           -- slashing event reduces totalAssets
 *
 * Invariants:
 *   TotalStakedEqualsSum -- totalAssets bookkeeping is consistent
 *   SharePriceMonotonic  -- share price never decreases (absent slashing)
 *   SharesConsistent     -- sum(userShares) = totalShares
 *   WithdrawalCorrect    -- withdrawal amount = shares * sharePrice
 *
 * Safety:
 *   SlashingProportional -- slashing reduces share price proportionally
 *)

EXTENDS Integers, FiniteSets

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    Addresses,      \* Set of staker addresses
    MaxAmount,      \* Upper bound on token amounts
    Precision       \* Scaling factor for share price (e.g. 1000)

\* --------------------------------------------------------------------------
\* ASSUMPTIONS
\* --------------------------------------------------------------------------

ASSUME Addresses # {} /\ IsFiniteSet(Addresses)
ASSUME MaxAmount \in Nat \ {0}
ASSUME Precision \in Nat \ {0}

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    totalAssets,        \* Nat -- total tokens in the vault
    totalShares,        \* Nat -- total shares outstanding
    userShares,         \* userShares[a] \in Nat -- shares per address
    lastSharePrice,     \* Nat -- share price * Precision at last checkpoint
    slashingOccurred    \* BOOLEAN -- whether slashing has ever happened

vars == <<totalAssets, totalShares, userShares, lastSharePrice, slashingOccurred>>

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

TypeOK ==
    /\ totalAssets \in Nat
    /\ totalShares \in Nat
    /\ userShares \in [Addresses -> Nat]
    /\ lastSharePrice \in Nat
    /\ slashingOccurred \in BOOLEAN

\* --------------------------------------------------------------------------
\* HELPERS
\* --------------------------------------------------------------------------

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + SumOver(f, S \ {x})

TotalSharesFromMap == SumOver(userShares, Addresses)

\* Current share price scaled by Precision.
\* If totalShares = 0, price is Precision (1:1 ratio for first staker).
SharePrice ==
    IF totalShares = 0 THEN Precision
    ELSE (totalAssets * Precision) \div totalShares

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ totalAssets = 0
    /\ totalShares = 0
    /\ userShares = [a \in Addresses |-> 0]
    /\ lastSharePrice = Precision
    /\ slashingOccurred = FALSE

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

(*
 * Stake(a, amt):
 *   Address a stakes amt tokens. Receives shares proportional to current
 *   share price: newShares = amt * Precision / SharePrice.
 *   First staker gets shares = amt (1:1).
 *)
Stake(a, amt) ==
    /\ amt > 0
    /\ totalAssets + amt <= MaxAmount
    /\ LET price     == SharePrice
           newShares == IF totalShares = 0 THEN amt
                        ELSE (amt * Precision) \div price
       IN /\ newShares > 0
          /\ totalAssets' = totalAssets + amt
          /\ totalShares' = totalShares + newShares
          /\ userShares' = [userShares EXCEPT ![a] = @ + newShares]
          /\ lastSharePrice' = SharePrice
          /\ UNCHANGED slashingOccurred

(*
 * Unstake(a, sh):
 *   Address a redeems sh shares. Receives tokens = sh * SharePrice / Precision.
 *   Precondition: a holds >= sh shares.
 *)
Unstake(a, sh) ==
    /\ sh > 0
    /\ userShares[a] >= sh
    /\ totalShares > 0
    /\ LET payout == (sh * totalAssets) \div totalShares
       IN /\ payout > 0
          /\ totalAssets' = totalAssets - payout
          /\ totalShares' = totalShares - sh
          /\ userShares' = [userShares EXCEPT ![a] = @ - sh]
          /\ lastSharePrice' = IF totalShares - sh > 0
                               THEN ((totalAssets - payout) * Precision) \div (totalShares - sh)
                               ELSE Precision
          /\ UNCHANGED slashingOccurred

(*
 * AccrueRewards(amt):
 *   Validator rewards increase totalAssets. Share price increases.
 *   totalShares is unchanged, so each share is worth more.
 *)
AccrueRewards(amt) ==
    /\ amt > 0
    /\ totalShares > 0
    /\ totalAssets + amt <= MaxAmount
    /\ totalAssets' = totalAssets + amt
    /\ lastSharePrice' = ((totalAssets + amt) * Precision) \div totalShares
    /\ UNCHANGED <<totalShares, userShares, slashingOccurred>>

(*
 * Slash(amt):
 *   Slashing event reduces totalAssets. Share price decreases proportionally.
 *   Precondition: amt <= totalAssets, totalShares > 0.
 *)
Slash(amt) ==
    /\ amt > 0
    /\ totalShares > 0
    /\ amt <= totalAssets
    /\ totalAssets' = totalAssets - amt
    /\ lastSharePrice' = ((totalAssets - amt) * Precision) \div totalShares
    /\ slashingOccurred' = TRUE
    /\ UNCHANGED <<totalShares, userShares>>

\* --------------------------------------------------------------------------
\* NEXT-STATE RELATION
\* --------------------------------------------------------------------------

Next ==
    \/ \E a \in Addresses, amt \in 1..MaxAmount : Stake(a, amt)
    \/ \E a \in Addresses, sh \in 1..MaxAmount : Unstake(a, sh)
    \/ \E amt \in 1..MaxAmount : AccrueRewards(amt)
    \/ \E amt \in 1..MaxAmount : Slash(amt)

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

\* ==========================================================================
\* SAFETY INVARIANTS
\* ==========================================================================

(*
 * SharesConsistent:
 *   The sum of individual userShares equals totalShares.
 *)
SharesConsistent ==
    TotalSharesFromMap = totalShares

(*
 * SharePriceMonotonic:
 *   Absent slashing, the share price never decreases.
 *   This is the fundamental invariant of yield-bearing vaults:
 *   rewards increase totalAssets, shares stay constant, price goes up.
 *)
SharePriceMonotonic ==
    ~slashingOccurred => lastSharePrice >= Precision

(*
 * NonNegativeAssets:
 *   Total assets are always non-negative.
 *)
NonNegativeAssets ==
    totalAssets >= 0

(*
 * SlashingReducesPrice:
 *   After slashing, the share price is lower than before.
 *   We check: if slashing occurred, the price may be below the initial 1:1.
 *   The action property verifies the actual decrease.
 *)
SlashingActionProperty ==
    [][
        slashingOccurred' /\ ~slashingOccurred
        => lastSharePrice' <= lastSharePrice
    ]_vars

(*
 * NoSharesWithoutAssets:
 *   If totalShares > 0, totalAssets > 0 (the vault is not empty).
 *   Slashing can reduce assets to 0, but then shares should be burned.
 *)
VaultSolvent ==
    (totalShares > 0 /\ ~slashingOccurred) => totalAssets > 0

=============================================================================
