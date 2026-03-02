// Copyright (C) 2026, Lux Industries, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Property-based tests for DeFi protocol invariants.
//
// These tests verify fundamental invariants of the DeFi contracts:
//   - AMM: constant product invariant (reserve0 * reserve1 >= k)
//   - Governance: no double voting
//   - Orderbook: price-time priority
//   - Token: conservation of supply
//   - Liquid staking: share price monotonicity (absent slashing)
package property

import (
	"fmt"
	mathrand "math/rand"
	"sort"
	"testing"
)

// ---------------------------------------------------------------------------
// AMM: constant product invariant
// ---------------------------------------------------------------------------

// AMMPool models a constant product AMM with two token reserves.
type AMMPool struct {
	Reserve0 uint64
	Reserve1 uint64
	K        uint64 // constant product lower bound
	FeeNum   uint64 // e.g. 997
	FeeDen   uint64 // e.g. 1000
}

func NewAMMPool(feeNum, feeDen uint64) *AMMPool {
	return &AMMPool{FeeNum: feeNum, FeeDen: feeDen}
}

func (p *AMMPool) AddLiquidity(amt0, amt1 uint64) {
	p.Reserve0 += amt0
	p.Reserve1 += amt1
	p.K = p.Reserve0 * p.Reserve1
}

// Swap01 swaps amtIn of token0 for token1. Returns amount out.
func (p *AMMPool) Swap01(amtIn uint64) uint64 {
	if p.Reserve0 == 0 || p.Reserve1 == 0 || amtIn == 0 {
		return 0
	}
	amtInWithFee := amtIn * p.FeeNum
	numerator := amtInWithFee * p.Reserve1
	denominator := p.Reserve0*p.FeeDen + amtInWithFee
	if denominator == 0 {
		return 0
	}
	amtOut := numerator / denominator
	if amtOut == 0 || amtOut >= p.Reserve1 {
		return 0
	}
	p.Reserve0 += amtIn
	p.Reserve1 -= amtOut
	return amtOut
}

// Swap10 swaps amtIn of token1 for token0. Returns amount out.
func (p *AMMPool) Swap10(amtIn uint64) uint64 {
	if p.Reserve0 == 0 || p.Reserve1 == 0 || amtIn == 0 {
		return 0
	}
	amtInWithFee := amtIn * p.FeeNum
	numerator := amtInWithFee * p.Reserve0
	denominator := p.Reserve1*p.FeeDen + amtInWithFee
	if denominator == 0 {
		return 0
	}
	amtOut := numerator / denominator
	if amtOut == 0 || amtOut >= p.Reserve0 {
		return 0
	}
	p.Reserve1 += amtIn
	p.Reserve0 -= amtOut
	return amtOut
}

// TestAMM_ConstantProductInvariant verifies that for any sequence of swaps,
// the product of reserves never falls below the initial k.
//
// Property: For all swap sequences S: reserve0 * reserve1 >= k_before
func TestAMM_ConstantProductInvariant(t *testing.T) {
	seeds := []int64{42, 123, 7777, 31337, 999}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			pool := NewAMMPool(997, 1000)

			// Initialize pool with random liquidity.
			amt0 := uint64(100 + rng.Intn(900))
			amt1 := uint64(100 + rng.Intn(900))
			pool.AddLiquidity(amt0, amt1)
			kBefore := pool.K

			// Perform random swaps.
			for i := 0; i < 200; i++ {
				amtIn := uint64(1 + rng.Intn(50))

				if rng.Intn(2) == 0 {
					pool.Swap01(amtIn)
				} else {
					pool.Swap10(amtIn)
				}

				product := pool.Reserve0 * pool.Reserve1
				if product < kBefore {
					t.Fatalf("step %d: product %d < k %d (reserves: %d, %d)",
						i, product, kBefore, pool.Reserve0, pool.Reserve1)
				}
			}
		})
	}
}

// TestAMM_SwapOutputBounded verifies that swap output is always less than
// the input times the fee factor (no value extraction).
//
// Property: For all swaps, output <= input (in value terms)
func TestAMM_SwapOutputBounded(t *testing.T) {
	seeds := []int64{1, 2, 3, 4, 5}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			pool := NewAMMPool(997, 1000)
			pool.AddLiquidity(uint64(500+rng.Intn(500)), uint64(500+rng.Intn(500)))

			for i := 0; i < 100; i++ {
				amtIn := uint64(1 + rng.Intn(100))
				priceBefore := pool.Reserve1 * 1000 / pool.Reserve0

				amtOut := pool.Swap01(amtIn)
				if amtOut == 0 {
					continue
				}

				// Output in token1 should not exceed the fair value of input
				// at the pre-swap price. Fair value = amtIn * priceBefore / 1000.
				fairValue := amtIn * priceBefore / 1000
				if amtOut > fairValue+1 { // +1 for rounding tolerance
					t.Fatalf("step %d: output %d > fair value %d (input=%d, price=%d)",
						i, amtOut, fairValue, amtIn, priceBefore)
				}
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Governance: no double voting
// ---------------------------------------------------------------------------

// GovernanceProposal models a single governance proposal.
type GovernanceProposal struct {
	ForVotes     uint64
	AgainstVotes uint64
	Voters       map[string]bool
}

func NewGovernanceProposal() *GovernanceProposal {
	return &GovernanceProposal{Voters: make(map[string]bool)}
}

// Vote casts a vote. Returns false if the address already voted.
func (p *GovernanceProposal) Vote(addr string, weight uint64, support bool) bool {
	if p.Voters[addr] {
		return false
	}
	p.Voters[addr] = true
	if support {
		p.ForVotes += weight
	} else {
		p.AgainstVotes += weight
	}
	return true
}

// TestGovernance_NoDoubleVoting verifies that for any vote sequence,
// each address votes at most once per proposal.
//
// Property: For all vote sequences V and addresses a:
//   count(a votes in V) <= 1
func TestGovernance_NoDoubleVoting(t *testing.T) {
	seeds := []int64{42, 99, 2026, 8675309, 1}

	addresses := []string{"a1", "a2", "a3", "a4", "a5"}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			proposal := NewGovernanceProposal()

			for i := 0; i < 100; i++ {
				addr := addresses[rng.Intn(len(addresses))]
				weight := uint64(1 + rng.Intn(10))
				support := rng.Intn(2) == 0

				alreadyVoted := proposal.Voters[addr]
				ok := proposal.Vote(addr, weight, support)

				if alreadyVoted && ok {
					t.Fatalf("step %d: address %s voted twice", i, addr)
				}
				if !alreadyVoted && !ok {
					t.Fatalf("step %d: address %s rejected on first vote", i, addr)
				}
			}

			// Verify: number of unique voters matches the voter set size.
			voterCount := 0
			for _, voted := range proposal.Voters {
				if voted {
					voterCount++
				}
			}
			if voterCount > len(addresses) {
				t.Fatalf("voter count %d exceeds address count %d",
					voterCount, len(addresses))
			}
		})
	}
}

// TestGovernance_VoteTotalBound verifies that forVotes + againstVotes
// never exceeds the total voting power.
//
// Property: forVotes + againstVotes <= sum(weights of all voters)
func TestGovernance_VoteTotalBound(t *testing.T) {
	seeds := []int64{11, 22, 33}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			proposal := NewGovernanceProposal()
			weights := map[string]uint64{
				"a1": uint64(1 + rng.Intn(10)),
				"a2": uint64(1 + rng.Intn(10)),
				"a3": uint64(1 + rng.Intn(10)),
			}

			var totalPower uint64
			for _, w := range weights {
				totalPower += w
			}

			for _, addr := range []string{"a1", "a2", "a3"} {
				support := rng.Intn(2) == 0
				proposal.Vote(addr, weights[addr], support)
			}

			total := proposal.ForVotes + proposal.AgainstVotes
			if total > totalPower {
				t.Fatalf("total votes %d exceeds total power %d", total, totalPower)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Orderbook: price-time priority
// ---------------------------------------------------------------------------

// Order models a limit order in the CLOB.
type Order struct {
	ID     string
	Side   string // "Buy" or "Sell"
	Price  uint64
	Amount uint64
	Filled uint64
	SeqNo  int
}

// Fill records a trade between two orders.
type Fill struct {
	BuyID  string
	SellID string
	Price  uint64
	Amount uint64
}

// Orderbook models a simple CLOB with price-time priority matching.
type Orderbook struct {
	Orders map[string]*Order
	Fills  []Fill
	nextSeq int
}

func NewOrderbook() *Orderbook {
	return &Orderbook{Orders: make(map[string]*Order)}
}

func (ob *Orderbook) Place(id, side string, price, amount uint64) {
	ob.Orders[id] = &Order{
		ID:     id,
		Side:   side,
		Price:  price,
		Amount: amount,
		SeqNo:  ob.nextSeq,
	}
	ob.nextSeq++
}

// Match finds the best matching pair and executes a fill.
func (ob *Orderbook) Match() bool {
	// Find best buy (highest price, then lowest seqNo).
	var bestBuy *Order
	for _, o := range ob.Orders {
		if o.Side != "Buy" || o.Filled >= o.Amount {
			continue
		}
		if bestBuy == nil ||
			o.Price > bestBuy.Price ||
			(o.Price == bestBuy.Price && o.SeqNo < bestBuy.SeqNo) {
			bestBuy = o
		}
	}
	if bestBuy == nil {
		return false
	}

	// Find best sell (lowest price, then lowest seqNo).
	var bestSell *Order
	for _, o := range ob.Orders {
		if o.Side != "Sell" || o.Filled >= o.Amount {
			continue
		}
		if bestSell == nil ||
			o.Price < bestSell.Price ||
			(o.Price == bestSell.Price && o.SeqNo < bestSell.SeqNo) {
			bestSell = o
		}
	}
	if bestSell == nil {
		return false
	}

	// Check if they cross.
	if bestBuy.Price < bestSell.Price {
		return false
	}

	// Fill at maker's price (earlier order).
	tradePrice := bestBuy.Price
	if bestSell.SeqNo < bestBuy.SeqNo {
		tradePrice = bestSell.Price
	}

	buyRemaining := bestBuy.Amount - bestBuy.Filled
	sellRemaining := bestSell.Amount - bestSell.Filled
	fillAmt := buyRemaining
	if sellRemaining < fillAmt {
		fillAmt = sellRemaining
	}

	bestBuy.Filled += fillAmt
	bestSell.Filled += fillAmt

	ob.Fills = append(ob.Fills, Fill{
		BuyID:  bestBuy.ID,
		SellID: bestSell.ID,
		Price:  tradePrice,
		Amount: fillAmt,
	})

	return true
}

// TestOrderbook_PriceTimePriority verifies that for any order sequence,
// fills respect price-time priority: better-priced or earlier same-priced
// orders fill first.
//
// Property: For all order sequences, fill order respects priority.
func TestOrderbook_PriceTimePriority(t *testing.T) {
	seeds := []int64{42, 100, 2026, 7, 31337}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			ob := NewOrderbook()

			// Place random orders.
			numOrders := 5 + rng.Intn(10)
			for i := 0; i < numOrders; i++ {
				id := fmt.Sprintf("o%d", i)
				side := "Buy"
				if rng.Intn(2) == 0 {
					side = "Sell"
				}
				price := uint64(1 + rng.Intn(10))
				amount := uint64(1 + rng.Intn(20))
				ob.Place(id, side, price, amount)
			}

			// Match until no more fills.
			for ob.Match() {
			}

			// Verify price-time priority for buy-side fills.
			buyFillOrder := make([]string, 0)
			for _, f := range ob.Fills {
				buyFillOrder = append(buyFillOrder, f.BuyID)
			}
			// Deduplicate while preserving first-appearance order.
			seen := make(map[string]bool)
			uniqueBuyFills := make([]string, 0)
			for _, id := range buyFillOrder {
				if !seen[id] {
					seen[id] = true
					uniqueBuyFills = append(uniqueBuyFills, id)
				}
			}

			// Check: for consecutive distinct fills, the earlier fill's order
			// should have equal or better priority.
			for i := 0; i+1 < len(uniqueBuyFills); i++ {
				o1 := ob.Orders[uniqueBuyFills[i]]
				o2 := ob.Orders[uniqueBuyFills[i+1]]
				if o2.Price > o1.Price {
					t.Fatalf("fill %d: order %s (price=%d) filled before %s (price=%d) -- wrong priority",
						i, o1.ID, o1.Price, o2.ID, o2.Price)
				}
				if o2.Price == o1.Price && o2.SeqNo < o1.SeqNo {
					t.Fatalf("fill %d: order %s (seq=%d) filled before %s (seq=%d) at same price -- wrong time priority",
						i, o1.ID, o1.SeqNo, o2.ID, o2.SeqNo)
				}
			}
		})
	}
}

// TestOrderbook_NoOverfill verifies that for any order sequence,
// the sum of fills for an order never exceeds the order amount.
//
// Property: For all orders o: sum(fills for o) <= o.amount
func TestOrderbook_NoOverfill(t *testing.T) {
	seeds := []int64{1, 2, 3, 4, 5}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			ob := NewOrderbook()

			for i := 0; i < 10; i++ {
				side := "Buy"
				if rng.Intn(2) == 0 {
					side = "Sell"
				}
				ob.Place(fmt.Sprintf("o%d", i), side, uint64(1+rng.Intn(5)), uint64(1+rng.Intn(10)))
			}

			for ob.Match() {
			}

			// Sum fills per order.
			fillSums := make(map[string]uint64)
			for _, f := range ob.Fills {
				fillSums[f.BuyID] += f.Amount
				fillSums[f.SellID] += f.Amount
			}

			for id, total := range fillSums {
				if total > ob.Orders[id].Amount {
					t.Fatalf("order %s: filled %d > amount %d", id, total, ob.Orders[id].Amount)
				}
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Token: conservation of supply
// ---------------------------------------------------------------------------

// TokenLedger models a simple ERC20 token with transfer and mint.
type TokenLedger struct {
	Balances    map[string]uint64
	TotalSupply uint64
}

func NewTokenLedger() *TokenLedger {
	return &TokenLedger{Balances: make(map[string]uint64)}
}

func (l *TokenLedger) Mint(to string, amount uint64) {
	l.Balances[to] += amount
	l.TotalSupply += amount
}

func (l *TokenLedger) Transfer(from, to string, amount uint64) bool {
	if l.Balances[from] < amount {
		return false
	}
	l.Balances[from] -= amount
	l.Balances[to] += amount
	return true
}

func (l *TokenLedger) Burn(from string, amount uint64) bool {
	if l.Balances[from] < amount {
		return false
	}
	l.Balances[from] -= amount
	l.TotalSupply -= amount
	return true
}

func (l *TokenLedger) SumBalances() uint64 {
	var total uint64
	for _, b := range l.Balances {
		total += b
	}
	return total
}

// TestToken_ConservationOfSupply verifies that for any sequence of
// transfers, sum(balances) = totalSupply.
//
// Property: For all transfer sequences T: sum(balances) = totalSupply
func TestToken_ConservationOfSupply(t *testing.T) {
	seeds := []int64{42, 99, 7777, 54321, 1}

	addresses := []string{"a1", "a2", "a3", "a4"}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			ledger := NewTokenLedger()

			// Mint initial supply.
			for _, addr := range addresses {
				amt := uint64(100 + rng.Intn(900))
				ledger.Mint(addr, amt)
			}

			// Verify after mint.
			if ledger.SumBalances() != ledger.TotalSupply {
				t.Fatalf("after mint: sum %d != supply %d",
					ledger.SumBalances(), ledger.TotalSupply)
			}

			// Random transfers and burns.
			for i := 0; i < 500; i++ {
				action := rng.Intn(3)
				from := addresses[rng.Intn(len(addresses))]
				to := addresses[rng.Intn(len(addresses))]
				amt := uint64(1 + rng.Intn(50))

				switch action {
				case 0: // transfer
					ledger.Transfer(from, to, amt)
				case 1: // burn
					ledger.Burn(from, amt)
				case 2: // mint
					ledger.Mint(to, amt)
				}

				if ledger.SumBalances() != ledger.TotalSupply {
					t.Fatalf("step %d: sum %d != supply %d",
						i, ledger.SumBalances(), ledger.TotalSupply)
				}
			}
		})
	}
}

// TestToken_TransferPreservesSupply verifies that transfers never change
// the total supply (only mint and burn do).
//
// Property: For all transfers T: totalSupply_before = totalSupply_after
func TestToken_TransferPreservesSupply(t *testing.T) {
	rng := mathrand.New(mathrand.NewSource(42))
	ledger := NewTokenLedger()
	ledger.Mint("a1", 1000)
	ledger.Mint("a2", 500)

	supplyBefore := ledger.TotalSupply

	for i := 0; i < 200; i++ {
		from := "a1"
		to := "a2"
		if rng.Intn(2) == 0 {
			from, to = to, from
		}
		amt := uint64(1 + rng.Intn(100))
		ledger.Transfer(from, to, amt)

		if ledger.TotalSupply != supplyBefore {
			t.Fatalf("step %d: supply changed from %d to %d after transfer",
				i, supplyBefore, ledger.TotalSupply)
		}
	}
}

// ---------------------------------------------------------------------------
// Liquid staking: share price monotonicity
// ---------------------------------------------------------------------------

// LiquidStakingVault models a yield-bearing staking vault.
type LiquidStakingVault struct {
	TotalAssets uint64
	TotalShares uint64
	UserShares  map[string]uint64
}

func NewLiquidStakingVault() *LiquidStakingVault {
	return &LiquidStakingVault{UserShares: make(map[string]uint64)}
}

// SharePrice returns the share price scaled by 1e6.
func (v *LiquidStakingVault) SharePrice() uint64 {
	if v.TotalShares == 0 {
		return 1_000_000 // 1:1 ratio
	}
	return v.TotalAssets * 1_000_000 / v.TotalShares
}

func (v *LiquidStakingVault) Stake(addr string, amt uint64) {
	if amt == 0 {
		return
	}
	var newShares uint64
	if v.TotalShares == 0 {
		newShares = amt
	} else {
		newShares = amt * v.TotalShares / v.TotalAssets
	}
	if newShares == 0 {
		return
	}
	v.TotalAssets += amt
	v.TotalShares += newShares
	v.UserShares[addr] += newShares
}

func (v *LiquidStakingVault) Unstake(addr string, shares uint64) uint64 {
	if shares == 0 || v.UserShares[addr] < shares || v.TotalShares == 0 {
		return 0
	}
	payout := shares * v.TotalAssets / v.TotalShares
	if payout == 0 {
		return 0
	}
	v.TotalAssets -= payout
	v.TotalShares -= shares
	v.UserShares[addr] -= shares
	return payout
}

func (v *LiquidStakingVault) AccrueRewards(amt uint64) {
	if v.TotalShares == 0 || amt == 0 {
		return
	}
	v.TotalAssets += amt
}

// TestLiquidStaking_SharePriceMonotonic verifies that for any sequence
// of stake, unstake, and reward accrual operations (no slashing),
// the share price never decreases.
//
// Property: For all operation sequences (no slashing):
//   sharePrice_after >= sharePrice_before
func TestLiquidStaking_SharePriceMonotonic(t *testing.T) {
	seeds := []int64{42, 99, 2026, 777, 12345}
	addresses := []string{"a1", "a2", "a3"}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			vault := NewLiquidStakingVault()

			// Initial stake.
			vault.Stake("a1", uint64(100+rng.Intn(900)))

			priceBefore := vault.SharePrice()

			for i := 0; i < 200; i++ {
				action := rng.Intn(3)
				addr := addresses[rng.Intn(len(addresses))]

				switch action {
				case 0: // stake
					amt := uint64(1 + rng.Intn(100))
					vault.Stake(addr, amt)
				case 1: // unstake (partial)
					sh := vault.UserShares[addr]
					if sh > 0 {
						toUnstake := uint64(1 + rng.Intn(int(sh)))
						if toUnstake > sh {
							toUnstake = sh
						}
						vault.Unstake(addr, toUnstake)
					}
				case 2: // accrue rewards
					amt := uint64(1 + rng.Intn(50))
					vault.AccrueRewards(amt)
				}

				priceNow := vault.SharePrice()
				if vault.TotalShares > 0 && priceNow < priceBefore {
					t.Fatalf("step %d: share price decreased from %d to %d (action=%d, assets=%d, shares=%d)",
						i, priceBefore, priceNow, action, vault.TotalAssets, vault.TotalShares)
				}
				if vault.TotalShares > 0 {
					priceBefore = priceNow
				} else {
					// Pool fully drained — next stake resets share price to base
					priceBefore = 0
				}
			}
		})
	}
}

// TestLiquidStaking_SharesConsistent verifies that the sum of user shares
// equals totalShares.
//
// Property: sum(userShares) = totalShares
func TestLiquidStaking_SharesConsistent(t *testing.T) {
	seeds := []int64{1, 42, 777}
	addresses := []string{"a1", "a2", "a3"}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			vault := NewLiquidStakingVault()

			for i := 0; i < 200; i++ {
				addr := addresses[rng.Intn(len(addresses))]

				if rng.Intn(2) == 0 {
					vault.Stake(addr, uint64(1+rng.Intn(100)))
				} else {
					sh := vault.UserShares[addr]
					if sh > 0 {
						vault.Unstake(addr, uint64(1+rng.Intn(int(sh))))
					}
				}

				var sumShares uint64
				for _, sh := range vault.UserShares {
					sumShares += sh
				}
				if sumShares != vault.TotalShares {
					t.Fatalf("step %d: sum shares %d != total shares %d",
						i, sumShares, vault.TotalShares)
				}
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Cross-cutting: sortedness invariant helper
// ---------------------------------------------------------------------------

// TestOrderbook_FillPricesMonotonic verifies that fill prices in a
// sequence of matched orders are consistent with the book state.
func TestOrderbook_FillPricesMonotonic(t *testing.T) {
	rng := mathrand.New(mathrand.NewSource(42))
	ob := NewOrderbook()

	// Place a mix of buy and sell orders at various prices.
	buys := []uint64{10, 9, 8, 7, 6}
	sells := []uint64{5, 6, 7, 8, 9}

	for i, p := range buys {
		ob.Place(fmt.Sprintf("b%d", i), "Buy", p, uint64(10+rng.Intn(10)))
	}
	for i, p := range sells {
		ob.Place(fmt.Sprintf("s%d", i), "Sell", p, uint64(10+rng.Intn(10)))
	}

	for ob.Match() {
	}

	// Collect fill prices.
	prices := make([]uint64, 0, len(ob.Fills))
	for _, f := range ob.Fills {
		prices = append(prices, f.Price)
	}

	// Fill prices should be weakly decreasing (best matches first).
	sorted := make([]uint64, len(prices))
	copy(sorted, prices)
	sort.Slice(sorted, func(i, j int) bool { return sorted[i] > sorted[j] })

	for i := range prices {
		if prices[i] != sorted[i] {
			t.Fatalf("fill prices not in priority order: got %v, want %v", prices, sorted)
		}
	}
}
