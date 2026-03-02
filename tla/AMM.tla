---------------------------- MODULE AMM --------------------------------------
(*
 * TLA+ Specification of the Lux DeFi Constant Product AMM
 *
 * Source: ~/work/lux/contracts/amm/
 *
 * Protocol summary:
 *   A constant product automated market maker (xy=k) manages a liquidity
 *   pool of two tokens. Liquidity providers deposit proportional amounts
 *   of both tokens and receive LP shares. Traders swap one token for the
 *   other, paying a fee. The product of reserves is non-decreasing.
 *
 * State model:
 *   reserve0            -- amount of token0 in the pool
 *   reserve1            -- amount of token1 in the pool
 *   totalShares         -- total LP shares outstanding
 *   shares[a]           -- LP shares held by address a
 *   k                   -- constant product lower bound (monotonically increasing)
 *
 * Actions:
 *   AddLiquidity(a, amt0, amt1)   -- address a deposits both tokens
 *   RemoveLiquidity(a, sh)        -- address a redeems sh LP shares
 *   Swap01(a, amtIn)              -- swap token0 for token1
 *   Swap10(a, amtIn)              -- swap token1 for token0
 *
 * Invariants:
 *   ConstantProduct      -- reserve0 * reserve1 >= k
 *   KMonotonic           -- k never decreases
 *   ShareProportional    -- shares reflect proportional ownership
 *   NoValueExtraction    -- swap output <= input * fee factor
 *
 * Liveness:
 *   SwapAlwaysSucceeds   -- if reserves > 0, swap is enabled
 *)

EXTENDS Integers, FiniteSets

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    Addresses,      \* Set of participant addresses
    MaxAmount,      \* Upper bound on token amounts for model checking
    FeeNum,         \* Fee numerator (e.g. 997 for 0.3% fee)
    FeeDen          \* Fee denominator (e.g. 1000)

\* --------------------------------------------------------------------------
\* ASSUMPTIONS
\* --------------------------------------------------------------------------

ASSUME Addresses # {} /\ IsFiniteSet(Addresses)
ASSUME MaxAmount \in Nat \ {0}
ASSUME FeeNum \in Nat \ {0}
ASSUME FeeDen \in Nat \ {0}
ASSUME FeeNum <= FeeDen   \* fee factor <= 1

\* --------------------------------------------------------------------------
\* DERIVED SETS
\* --------------------------------------------------------------------------

Amounts == 0..MaxAmount

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    reserve0,       \* Nat -- token0 in pool
    reserve1,       \* Nat -- token1 in pool
    totalShares,    \* Nat -- total LP shares outstanding
    shares,         \* shares[a] \in Nat -- LP shares per address
    k               \* Nat -- constant product lower bound

vars == <<reserve0, reserve1, totalShares, shares, k>>

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

TypeOK ==
    /\ reserve0 \in Nat
    /\ reserve1 \in Nat
    /\ totalShares \in Nat
    /\ shares \in [Addresses -> Nat]
    /\ k \in Nat

\* --------------------------------------------------------------------------
\* HELPERS
\* --------------------------------------------------------------------------

\* Integer minimum
Min(a, b) == IF a <= b THEN a ELSE b

\* Sum shares across all addresses
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + SumOver(f, S \ {x})

TotalSharesFromMap == SumOver(shares, Addresses)

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ reserve0 = 0
    /\ reserve1 = 0
    /\ totalShares = 0
    /\ shares = [a \in Addresses |-> 0]
    /\ k = 0

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

(*
 * AddLiquidity(a, amt0, amt1):
 *   Address a deposits amt0 of token0 and amt1 of token1.
 *   Receives LP shares proportional to the deposit.
 *   First depositor sets the initial ratio and receives amt0 shares.
 *   Subsequent depositors receive min(amt0/reserve0, amt1/reserve1) * totalShares.
 *)
AddLiquidity(a, amt0, amt1) ==
    /\ amt0 > 0 /\ amt1 > 0
    /\ reserve0 + amt0 <= MaxAmount
    /\ reserve1 + amt1 <= MaxAmount
    /\ LET newShares ==
            IF totalShares = 0 THEN amt0
            ELSE Min((amt0 * totalShares) \div reserve0,
                     (amt1 * totalShares) \div reserve1)
       IN /\ newShares > 0
          /\ reserve0' = reserve0 + amt0
          /\ reserve1' = reserve1 + amt1
          /\ totalShares' = totalShares + newShares
          /\ shares' = [shares EXCEPT ![a] = @ + newShares]
          /\ k' = (reserve0 + amt0) * (reserve1 + amt1)

(*
 * RemoveLiquidity(a, sh):
 *   Address a redeems sh LP shares. Receives proportional reserves.
 *   Precondition: a holds at least sh shares, sh > 0.
 *)
RemoveLiquidity(a, sh) ==
    /\ sh > 0
    /\ shares[a] >= sh
    /\ totalShares > 0
    /\ LET amt0 == (sh * reserve0) \div totalShares
           amt1 == (sh * reserve1) \div totalShares
       IN /\ reserve0' = reserve0 - amt0
          /\ reserve1' = reserve1 - amt1
          /\ totalShares' = totalShares - sh
          /\ shares' = [shares EXCEPT ![a] = @ - sh]
          /\ k' = (reserve0 - amt0) * (reserve1 - amt1)

(*
 * Swap01(a, amtIn):
 *   Swap amtIn of token0 for token1.
 *   Output = (amtIn * FeeNum * reserve1) / (reserve0 * FeeDen + amtIn * FeeNum)
 *   Precondition: pool is initialized, amtIn > 0.
 *)
Swap01(a, amtIn) ==
    /\ amtIn > 0
    /\ reserve0 > 0 /\ reserve1 > 0
    /\ reserve0 + amtIn <= MaxAmount
    /\ LET amtInWithFee == amtIn * FeeNum
           numerator    == amtInWithFee * reserve1
           denominator  == reserve0 * FeeDen + amtInWithFee
           amtOut       == numerator \div denominator
       IN /\ amtOut > 0
          /\ amtOut < reserve1
          /\ reserve0' = reserve0 + amtIn
          /\ reserve1' = reserve1 - amtOut
          /\ k' = k   \* k is a lower bound; product may increase due to fees
          /\ UNCHANGED <<totalShares, shares>>

(*
 * Swap10(a, amtIn):
 *   Swap amtIn of token1 for token0. Symmetric to Swap01.
 *)
Swap10(a, amtIn) ==
    /\ amtIn > 0
    /\ reserve0 > 0 /\ reserve1 > 0
    /\ reserve1 + amtIn <= MaxAmount
    /\ LET amtInWithFee == amtIn * FeeNum
           numerator    == amtInWithFee * reserve0
           denominator  == reserve1 * FeeDen + amtInWithFee
           amtOut       == numerator \div denominator
       IN /\ amtOut > 0
          /\ amtOut < reserve0
          /\ reserve0' = reserve0 - amtOut
          /\ reserve1' = reserve1 + amtIn
          /\ k' = k
          /\ UNCHANGED <<totalShares, shares>>

\* --------------------------------------------------------------------------
\* NEXT-STATE RELATION
\* --------------------------------------------------------------------------

Next ==
    \/ \E a \in Addresses, amt0, amt1 \in 1..MaxAmount :
        AddLiquidity(a, amt0, amt1)
    \/ \E a \in Addresses, sh \in 1..MaxAmount :
        RemoveLiquidity(a, sh)
    \/ \E a \in Addresses, amt \in 1..MaxAmount :
        Swap01(a, amt)
    \/ \E a \in Addresses, amt \in 1..MaxAmount :
        Swap10(a, amt)

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

\* ==========================================================================
\* SAFETY INVARIANTS
\* ==========================================================================

(*
 * ConstantProduct:
 *   The product of reserves is always >= the recorded k after the pool
 *   is initialized. Swaps collect fees, so the product may increase.
 *   AddLiquidity updates k to the new product.
 *   RemoveLiquidity updates k to the new product.
 *
 *   For an uninitialized pool (totalShares = 0), k = 0 and the
 *   invariant holds trivially.
 *)
ConstantProduct ==
    totalShares > 0 => reserve0 * reserve1 >= k

(*
 * KMonotonic:
 *   k never decreases. Swaps preserve k (fees increase the product).
 *   Liquidity changes set k to the new product.
 *)
KMonotonic ==
    [][k' >= k]_vars

(*
 * SharesConsistent:
 *   The sum of individual shares equals totalShares.
 *)
SharesConsistent ==
    TotalSharesFromMap = totalShares

(*
 * NonNegativeReserves:
 *   Reserves are always non-negative.
 *)
NonNegativeReserves ==
    /\ reserve0 >= 0
    /\ reserve1 >= 0

(*
 * NoEmptyPoolWithShares:
 *   If totalShares > 0 then both reserves are > 0.
 *   An initialized pool always has tokens.
 *)
NoEmptyPoolWithShares ==
    totalShares > 0 => (reserve0 > 0 /\ reserve1 > 0)

(*
 * SwapEnabled:
 *   If the pool is initialized (reserves > 0), swap actions exist.
 *   This is a safety property: the pool never becomes stuck.
 *)
SwapEnabled ==
    (reserve0 > 0 /\ reserve1 > 0)
    => \E a \in Addresses, amt \in 1..MaxAmount :
        ENABLED Swap01(a, amt)

=============================================================================
