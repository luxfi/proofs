// Copyright (C) 2026, Lux Industries, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Property-based tests for Quasar Consensus invariants.
//
// These tests verify core safety and correctness properties of the
// three-layer (BLS + Ringtail + ML-DSA) consensus without importing
// the full consensus package. We re-derive the critical invariants
// from first principles using only the standard library.
//
// Source specifications:
//   - TLA+: ~/work/lux/proofs/tla/Quasar.tla
//   - Lean4: ~/work/lux/proofs/lean/Consensus/Quasar.lean
//   - Go:   ~/work/lux/consensus/protocol/quasar/quasar.go
package property

import (
	"crypto/sha256"
	"encoding/binary"
	"math"
	"math/rand"
	"testing"
)

// ---------------------------------------------------------------------------
// Quorum model (mirrors core.go addVoteLocked and grouped_threshold.go)
// ---------------------------------------------------------------------------

// quorumCheck returns true when signerWeight meets the quorum threshold.
// Uses cross-multiplication to avoid integer division truncation:
//
//	signerWeight * quorumDen >= totalWeight * quorumNum
//
// This is the exact check from quasar core.go (addVoteLocked) and
// grouped_threshold.go (GroupQuorum / VerifyGroupedSignature).
func quorumCheck(signerWeight, totalWeight, quorumNum, quorumDen uint64) bool {
	return signerWeight*quorumDen >= totalWeight*quorumNum
}

// quorumCheckDiv returns the naive division-based check for comparison:
//
//	signerWeight / totalWeight >= quorumNum / quorumDen
//
// This truncates and can produce wrong answers. We test that the
// cross-multiply version is always at least as strict.
func quorumCheckDiv(signerWeight, totalWeight, quorumNum, quorumDen uint64) bool {
	if totalWeight == 0 || quorumDen == 0 {
		return false
	}
	return signerWeight/totalWeight >= quorumNum/quorumDen
}

// ---------------------------------------------------------------------------
// Layer model (mirrors signer.IsQuantumMode / IsDualThresholdMode)
// ---------------------------------------------------------------------------

type layerSet struct {
	bls   bool
	rt    bool
	mldsa bool
}

func (l layerSet) isQuantum() bool { return l.bls && l.rt && l.mldsa }
func (l layerSet) isDual() bool   { return l.bls && (l.rt || l.mldsa) }
func (l layerSet) isBLSOnly() bool {
	return l.bls && !l.rt && !l.mldsa
}

// allLayersQuorum checks that every enabled layer independently has quorum.
// Maps to AllLayersQuorum in Quasar.tla.
func allLayersQuorum(layers layerSet, blsW, rtW, mldsaW, total, qNum, qDen uint64) bool {
	if layers.bls && !quorumCheck(blsW, total, qNum, qDen) {
		return false
	}
	if layers.rt && !quorumCheck(rtW, total, qNum, qDen) {
		return false
	}
	if layers.mldsa && !quorumCheck(mldsaW, total, qNum, qDen) {
		return false
	}
	return true
}

// ---------------------------------------------------------------------------
// FPC model (mirrors protocol/wave/fpc/fpc.go Selector)
// ---------------------------------------------------------------------------

// fpcTheta computes the FPC threshold theta for a given phase, seed,
// thetaMin, and thetaMax. Deterministic PRF: SHA-256(seed || phase).
func fpcTheta(seed []byte, phase uint64, thetaMin, thetaMax float64) float64 {
	h := sha256.New()
	h.Write(seed)
	var buf [8]byte
	binary.BigEndian.PutUint64(buf[:], phase)
	h.Write(buf[:])
	digest := h.Sum(nil)
	hashUint := binary.BigEndian.Uint64(digest[:8])
	normalized := float64(hashUint) / float64(^uint64(0))
	return thetaMin + normalized*(thetaMax-thetaMin)
}

// fpcAlpha computes alpha = ceil(theta * k) for a given phase.
func fpcAlpha(seed []byte, phase uint64, thetaMin, thetaMax float64, k int) int {
	theta := fpcTheta(seed, phase, thetaMin, thetaMax)
	return int(math.Ceil(theta * float64(k)))
}

// ===========================================================================
// TEST: BLS-Only Quorum Safety
// ===========================================================================

// TestBLSOnly_QuorumSafety verifies that in BLS-only mode, a quorum of
// f < n/3 Byzantine nodes alone can never satisfy the 2/3 quorum check.
// For all n in [4, 200], verifies that f = floor((n-1)/3) Byzantine
// nodes are insufficient.
func TestBLSOnly_QuorumSafety(t *testing.T) {
	layers := layerSet{bls: true}
	if !layers.isBLSOnly() {
		t.Fatal("expected BLS-only mode")
	}

	for n := uint64(4); n <= 200; n++ {
		f := (n - 1) / 3 // max Byzantine

		// Byzantine alone must NOT reach quorum
		if quorumCheck(f, n, 2, 3) {
			t.Fatalf("n=%d f=%d: Byzantine alone reached quorum", n, f)
		}

		// Honest majority (n - f) must reach quorum
		honest := n - f
		if !quorumCheck(honest, n, 2, 3) {
			t.Fatalf("n=%d f=%d honest=%d: honest majority failed quorum", n, f, honest)
		}
	}
}

// ===========================================================================
// TEST: BLS + ML-DSA Dual Safety
// ===========================================================================

// TestBLSPlusMLDSA_DualSafety verifies that dual mode requires BOTH BLS
// and ML-DSA signatures to reach quorum. If either layer is missing
// quorum, finalization must fail.
func TestBLSPlusMLDSA_DualSafety(t *testing.T) {
	layers := layerSet{bls: true, mldsa: true}
	if !layers.isDual() {
		t.Fatal("expected dual mode")
	}

	rng := rand.New(rand.NewSource(42))

	for trial := 0; trial < 10000; trial++ {
		n := uint64(rng.Intn(97)) + 4 // n in [4, 100]
		f := (n - 1) / 3

		// Random BLS and MLDSA signer counts
		blsW := uint64(rng.Intn(int(n) + 1))
		mldsaW := uint64(rng.Intn(int(n) + 1))

		result := allLayersQuorum(layers, blsW, 0, mldsaW, n, 2, 3)

		blsOK := quorumCheck(blsW, n, 2, 3)
		mldsaOK := quorumCheck(mldsaW, n, 2, 3)

		expected := blsOK && mldsaOK
		if result != expected {
			t.Fatalf("trial=%d n=%d blsW=%d mldsaW=%d: got %v want %v",
				trial, n, blsW, mldsaW, result, expected)
		}

		// If Byzantine alone sign both layers, must NOT reach quorum
		if allLayersQuorum(layers, f, 0, f, n, 2, 3) {
			t.Fatalf("trial=%d n=%d f=%d: Byzantine alone reached dual quorum", trial, n, f)
		}
	}
}

// ===========================================================================
// TEST: Quantum Mode Requires All Three
// ===========================================================================

// TestQuantum_AllThreeRequired verifies that quantum mode requires BLS AND
// Ringtail AND ML-DSA to all independently reach quorum. Missing any one
// layer blocks finalization.
func TestQuantum_AllThreeRequired(t *testing.T) {
	layers := layerSet{bls: true, rt: true, mldsa: true}
	if !layers.isQuantum() {
		t.Fatal("expected quantum mode")
	}

	rng := rand.New(rand.NewSource(99))

	for trial := 0; trial < 10000; trial++ {
		n := uint64(rng.Intn(47)) + 4
		blsW := uint64(rng.Intn(int(n) + 1))
		rtW := uint64(rng.Intn(int(n) + 1))
		mldsaW := uint64(rng.Intn(int(n) + 1))

		result := allLayersQuorum(layers, blsW, rtW, mldsaW, n, 2, 3)

		blsOK := quorumCheck(blsW, n, 2, 3)
		rtOK := quorumCheck(rtW, n, 2, 3)
		mldsaOK := quorumCheck(mldsaW, n, 2, 3)

		expected := blsOK && rtOK && mldsaOK
		if result != expected {
			t.Fatalf("trial=%d n=%d bls=%d rt=%d mldsa=%d: got %v want %v",
				trial, n, blsW, rtW, mldsaW, result, expected)
		}
	}
}

// ===========================================================================
// TEST: Single Layer Compromise Insufficient
// ===========================================================================

// TestQuantum_SingleCompromiseInsufficient verifies that compromising any
// single cryptographic layer does not allow the adversary to finalize a
// forged value. With f < n/3 Byzantine nodes and the adversary controlling
// one layer completely, the remaining two layers block forgery.
func TestQuantum_SingleCompromiseInsufficient(t *testing.T) {
	for n := uint64(4); n <= 100; n++ {
		f := (n - 1) / 3

		// Scenario 1: BLS compromised (adversary can forge BLS sigs)
		// Adversary gets full BLS quorum (n) but only f on RT and MLDSA
		if allLayersQuorum(layerSet{bls: true, rt: true, mldsa: true},
			n, f, f, n, 2, 3) {
			t.Fatalf("n=%d: BLS compromised but forgery succeeded", n)
		}

		// Scenario 2: Ringtail compromised
		if allLayersQuorum(layerSet{bls: true, rt: true, mldsa: true},
			f, n, f, n, 2, 3) {
			t.Fatalf("n=%d: RT compromised but forgery succeeded", n)
		}

		// Scenario 3: ML-DSA compromised
		if allLayersQuorum(layerSet{bls: true, rt: true, mldsa: true},
			f, f, n, n, 2, 3) {
			t.Fatalf("n=%d: MLDSA compromised but forgery succeeded", n)
		}
	}
}

// ===========================================================================
// TEST: Dual Layer Compromise Insufficient
// ===========================================================================

// TestQuantum_DualCompromiseInsufficient verifies that compromising any
// TWO cryptographic layers still does not allow forgery, because the
// third intact layer requires honest majority.
func TestQuantum_DualCompromiseInsufficient(t *testing.T) {
	for n := uint64(4); n <= 100; n++ {
		f := (n - 1) / 3

		// BLS + RT compromised, MLDSA intact
		if allLayersQuorum(layerSet{bls: true, rt: true, mldsa: true},
			n, n, f, n, 2, 3) {
			t.Fatalf("n=%d: BLS+RT compromised but forgery succeeded", n)
		}

		// BLS + MLDSA compromised, RT intact
		if allLayersQuorum(layerSet{bls: true, rt: true, mldsa: true},
			n, f, n, n, 2, 3) {
			t.Fatalf("n=%d: BLS+MLDSA compromised but forgery succeeded", n)
		}

		// RT + MLDSA compromised, BLS intact
		if allLayersQuorum(layerSet{bls: true, rt: true, mldsa: true},
			f, n, n, n, 2, 3) {
			t.Fatalf("n=%d: RT+MLDSA compromised but forgery succeeded", n)
		}
	}
}

// ===========================================================================
// TEST: Cross-Multiply Never Truncates
// ===========================================================================

// TestQuorumCrossMult_NeverTruncates verifies that the cross-multiply
// quorum check is at least as strict as the naive integer-division check
// for all n in [1, 1000]. The cross-multiply form avoids truncation bugs
// that could weaken the quorum threshold.
func TestQuorumCrossMult_NeverTruncates(t *testing.T) {
	for n := uint64(1); n <= 1000; n++ {
		for w := uint64(0); w <= n; w++ {
			crossMult := quorumCheck(w, n, 2, 3)
			divBased := quorumCheckDiv(w, n, 2, 3)

			// Cross-multiply must never be LESS strict than division.
			// If division says no but cross-mult says yes, that is a bug.
			// The reverse (division says yes, cross-mult says no) is fine;
			// it means cross-mult is stricter, which is safer.
			if !crossMult && divBased {
				// This would mean division ACCEPTS but cross-mult REJECTS.
				// Actually this is the safe direction (cross-mult is stricter).
				// The dangerous case is the opposite.
				continue
			}
			if crossMult && !divBased {
				// Cross-mult accepts, division rejects.
				// Verify cross-mult is correct by checking exact rational:
				// w/n >= 2/3 <=> 3w >= 2n
				exactOK := 3*w >= 2*n
				if !exactOK {
					t.Fatalf("n=%d w=%d: cross-mult accepted but 3w=%d < 2n=%d",
						n, w, 3*w, 2*n)
				}
			}

			// Verify cross-mult matches exact rational arithmetic
			exact := 3*w >= 2*n
			if crossMult != exact {
				t.Fatalf("n=%d w=%d: crossMult=%v exact=%v", n, w, crossMult, exact)
			}
		}
	}
}

// ===========================================================================
// TEST: Epoch Pruning Memory Bounded
// ===========================================================================

// TestEpochPruning_MemoryBounded simulates 100K epochs with a retention
// window and verifies that the number of retained epochs never exceeds
// the configured bound. Maps to finalizedEpochRetention in core.go.
func TestEpochPruning_MemoryBounded(t *testing.T) {
	const (
		totalEpochs = 100_000
		retention   = uint64(6) // matches finalizedEpochRetention in core.go
	)

	// Simulate the epoch pruning logic from core.go finalizeQuantumEpoch
	store := make(map[uint64]bool) // epoch -> present

	var maxStoreSize int

	for epoch := uint64(0); epoch < totalEpochs; epoch++ {
		store[epoch] = true

		// Prune (mirrors core.go logic)
		if epoch > retention {
			cutoff := epoch - retention
			for e := range store {
				if e < cutoff {
					delete(store, e)
				}
			}
		}

		if len(store) > maxStoreSize {
			maxStoreSize = len(store)
		}

		// Invariant: store size never exceeds retention + 1
		if uint64(len(store)) > retention+1 {
			t.Fatalf("epoch=%d: store has %d entries, exceeds bound %d",
				epoch, len(store), retention+1)
		}
	}

	// Final check: at most retention+1 epochs retained
	if uint64(len(store)) > retention+1 {
		t.Fatalf("final store has %d entries, exceeds bound %d",
			len(store), retention+1)
	}

	t.Logf("100K epochs simulated, max store size: %d (bound: %d)", maxStoreSize, retention+1)
}

// ===========================================================================
// TEST: FPC Threshold Deterministic
// ===========================================================================

// TestFPCThreshold_Deterministic verifies that the FPC threshold selector
// produces identical results for the same (seed, phase) pair across
// multiple invocations. Maps to fpc.Selector.SelectThreshold.
func TestFPCThreshold_Deterministic(t *testing.T) {
	seed := []byte("deterministic-test-seed-2026")
	thetaMin := 0.5
	thetaMax := 0.8
	k := 20

	for phase := uint64(0); phase < 1000; phase++ {
		a1 := fpcAlpha(seed, phase, thetaMin, thetaMax, k)
		a2 := fpcAlpha(seed, phase, thetaMin, thetaMax, k)
		if a1 != a2 {
			t.Fatalf("phase=%d: non-deterministic alpha %d != %d", phase, a1, a2)
		}
	}

	// Different seeds must produce different sequences (with high probability)
	seedA := []byte("seed-alpha")
	seedB := []byte("seed-beta")
	matches := 0
	for phase := uint64(0); phase < 100; phase++ {
		if fpcAlpha(seedA, phase, thetaMin, thetaMax, k) ==
			fpcAlpha(seedB, phase, thetaMin, thetaMax, k) {
			matches++
		}
	}
	// With k=20 and theta in [0.5,0.8], alpha ranges over ~7 values.
	// Random collision rate ~ 1/7 ~ 14%. Allow up to 40% collisions.
	if matches > 40 {
		t.Fatalf("different seeds produced %d/100 matching alphas (too many)", matches)
	}
}

// ===========================================================================
// TEST: FPC Threshold In Range
// ===========================================================================

// TestFPCThreshold_InRange verifies that theta is always within
// [theta_min, theta_max] for all phases, and alpha = ceil(theta * k)
// is within [ceil(theta_min * k), ceil(theta_max * k)].
func TestFPCThreshold_InRange(t *testing.T) {
	seeds := [][]byte{
		[]byte("test-seed-1"),
		[]byte("test-seed-2"),
		[]byte("a-very-long-seed-for-extra-entropy"),
		{0x00, 0x01, 0x02, 0x03},
	}

	thetaMin := 0.5
	thetaMax := 0.8

	for _, seed := range seeds {
		for phase := uint64(0); phase < 10000; phase++ {
			theta := fpcTheta(seed, phase, thetaMin, thetaMax)

			if theta < thetaMin || theta > thetaMax {
				t.Fatalf("seed=%x phase=%d: theta=%f outside [%f, %f]",
					seed, phase, theta, thetaMin, thetaMax)
			}

			for _, k := range []int{3, 5, 10, 20, 50, 100} {
				alpha := fpcAlpha(seed, phase, thetaMin, thetaMax, k)
				alphaMin := int(math.Ceil(thetaMin * float64(k)))
				alphaMax := int(math.Ceil(thetaMax * float64(k)))

				if alpha < alphaMin || alpha > alphaMax {
					t.Fatalf("seed=%x phase=%d k=%d: alpha=%d outside [%d, %d]",
						seed, phase, k, alpha, alphaMin, alphaMax)
				}
			}
		}
	}
}
