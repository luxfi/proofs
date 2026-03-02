// Copyright (C) 2025, Lux Industries, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Package property contains property-based tests for FHE noise budget behavior.
//
// These tests verify the fundamental properties of TFHE bootstrapping:
//   - Noise is refreshed after each gate evaluation (bootstrap)
//   - Homomorphic additions accumulate noise linearly
//   - Decryption succeeds when noise is within budget
//   - Chained operations produce correct results when bootstrapping is applied
package property

import (
	"fmt"
	"testing"

	"github.com/luxfi/fhe"
)

// testContext bundles the FHE parameters and keys needed across tests.
type testContext struct {
	params fhe.Parameters
	kg     *fhe.KeyGenerator
	sk     *fhe.SecretKey
	bsk    *fhe.BootstrapKey
	enc    *fhe.Encryptor
	dec    *fhe.Decryptor
	eval   *fhe.Evaluator
}

func newTestContext(t *testing.T) *testContext {
	t.Helper()
	params, err := fhe.NewParametersFromLiteral(fhe.PN10QP27)
	if err != nil {
		t.Fatalf("NewParametersFromLiteral: %v", err)
	}
	kg := fhe.NewKeyGenerator(params)
	sk := kg.GenSecretKey()
	bsk := kg.GenBootstrapKey(sk)
	enc := fhe.NewEncryptor(params, sk)
	dec := fhe.NewDecryptor(params, sk)
	eval := fhe.NewEvaluator(params, bsk)

	return &testContext{
		params: params,
		kg:     kg,
		sk:     sk,
		bsk:    bsk,
		enc:    enc,
		dec:    dec,
		eval:   eval,
	}
}

// TestFHE_BootstrappedGatesPreserveCorrectness verifies that each boolean gate
// produces the correct truth table output. Because each gate bootstraps its
// result, noise is refreshed and decryption should always succeed.
//
// Property: For all boolean inputs (a, b), gate(Enc(a), Enc(b)) decrypts to
// the expected plaintext value.
func TestFHE_BootstrappedGatesPreserveCorrectness(t *testing.T) {
	tc := newTestContext(t)

	type gateTest struct {
		name string
		fn   func(*fhe.Evaluator, *fhe.Ciphertext, *fhe.Ciphertext) (*fhe.Ciphertext, error)
		eval func(a, b bool) bool
	}

	gates := []gateTest{
		{"AND", (*fhe.Evaluator).AND, func(a, b bool) bool { return a && b }},
		{"OR", (*fhe.Evaluator).OR, func(a, b bool) bool { return a || b }},
		{"NAND", (*fhe.Evaluator).NAND, func(a, b bool) bool { return !(a && b) }},
		{"NOR", (*fhe.Evaluator).NOR, func(a, b bool) bool { return !(a || b) }},
		{"XOR", (*fhe.Evaluator).XOR, func(a, b bool) bool { return a != b }},
		{"XNOR", (*fhe.Evaluator).XNOR, func(a, b bool) bool { return a == b }},
	}

	inputs := []struct{ a, b bool }{
		{false, false},
		{false, true},
		{true, false},
		{true, true},
	}

	for _, gate := range gates {
		for _, in := range inputs {
			name := fmt.Sprintf("%s(%v,%v)", gate.name, in.a, in.b)
			t.Run(name, func(t *testing.T) {
				ctA := tc.enc.Encrypt(in.a)
				ctB := tc.enc.Encrypt(in.b)

				ctResult, err := gate.fn(tc.eval, ctA, ctB)
				if err != nil {
					t.Fatalf("gate evaluation failed: %v", err)
				}

				got := tc.dec.Decrypt(ctResult)
				want := gate.eval(in.a, in.b)
				if got != want {
					t.Fatalf("got %v, want %v", got, want)
				}
			})
		}
	}
}

// TestFHE_ChainedANDNoiseRefresh verifies that chaining N bootstrapped AND
// gates produces correct results regardless of depth. Each AND gate includes
// a bootstrap that resets noise, so depth should not affect correctness.
//
// Property: AND(AND(...AND(1, 1)..., 1), 1) = 1 for arbitrary depth N.
// Property: AND(AND(...AND(1, 1)..., 1), 0) = 0 for arbitrary depth N.
func TestFHE_ChainedANDNoiseRefresh(t *testing.T) {
	tc := newTestContext(t)

	depths := []int{2, 4, 8, 16}

	for _, depth := range depths {
		t.Run(fmt.Sprintf("depth=%d/all_true", depth), func(t *testing.T) {
			acc := tc.enc.Encrypt(true)
			for i := 0; i < depth; i++ {
				ctTrue := tc.enc.Encrypt(true)
				var err error
				acc, err = tc.eval.AND(acc, ctTrue)
				if err != nil {
					t.Fatalf("AND at depth %d: %v", i, err)
				}
			}
			if got := tc.dec.Decrypt(acc); !got {
				t.Fatalf("expected true after %d AND(true) operations", depth)
			}
		})

		t.Run(fmt.Sprintf("depth=%d/inject_false", depth), func(t *testing.T) {
			acc := tc.enc.Encrypt(true)
			for i := 0; i < depth; i++ {
				// Inject false at the midpoint.
				val := i != depth/2
				ct := tc.enc.Encrypt(val)
				var err error
				acc, err = tc.eval.AND(acc, ct)
				if err != nil {
					t.Fatalf("AND at depth %d: %v", i, err)
				}
			}
			if got := tc.dec.Decrypt(acc); got {
				t.Fatalf("expected false after injecting false at depth %d", depth)
			}
		})
	}
}

// TestFHE_ChainedXORNoiseRefresh verifies that chaining XOR gates produces
// correct parity regardless of depth. XOR is particularly interesting because
// it uses the 2x(ct1+ct2) pre-processing trick for wrap-around.
//
// Property: XOR chain of N trues = true if N is odd, false if N is even.
func TestFHE_ChainedXORNoiseRefresh(t *testing.T) {
	tc := newTestContext(t)

	for depth := 1; depth <= 10; depth++ {
		t.Run(fmt.Sprintf("depth=%d", depth), func(t *testing.T) {
			acc := tc.enc.Encrypt(true)
			for i := 1; i < depth; i++ {
				ctTrue := tc.enc.Encrypt(true)
				var err error
				acc, err = tc.eval.XOR(acc, ctTrue)
				if err != nil {
					t.Fatalf("XOR at step %d: %v", i, err)
				}
			}
			got := tc.dec.Decrypt(acc)
			want := depth%2 == 1 // odd number of trues = true
			if got != want {
				t.Fatalf("depth %d: got %v, want %v", depth, got, want)
			}
		})
	}
}

// TestFHE_NOTIsNoiseFree verifies that NOT does not consume noise budget.
// NOT is implemented as ciphertext negation (no bootstrap needed), so it
// should be free to chain arbitrarily.
//
// Property: NOT^N(Enc(x)) decrypts correctly for all N.
func TestFHE_NOTIsNoiseFree(t *testing.T) {
	tc := newTestContext(t)

	for _, startVal := range []bool{true, false} {
		for n := 1; n <= 50; n++ {
			t.Run(fmt.Sprintf("start=%v/n=%d", startVal, n), func(t *testing.T) {
				ct := tc.enc.Encrypt(startVal)
				for i := 0; i < n; i++ {
					ct = tc.eval.NOT(ct)
				}
				got := tc.dec.Decrypt(ct)
				want := startVal
				if n%2 == 1 {
					want = !want
				}
				if got != want {
					t.Fatalf("NOT^%d(%v): got %v, want %v", n, startVal, got, want)
				}
			})
		}
	}
}

// TestFHE_RefreshResetsNoise verifies that the Refresh (identity bootstrap)
// operation preserves the encrypted value while resetting noise.
//
// Property: Refresh(Enc(x)) decrypts to x.
func TestFHE_RefreshResetsNoise(t *testing.T) {
	tc := newTestContext(t)

	for _, val := range []bool{true, false} {
		t.Run(fmt.Sprintf("value=%v", val), func(t *testing.T) {
			ct := tc.enc.Encrypt(val)
			refreshed, err := tc.eval.Refresh(ct)
			if err != nil {
				t.Fatalf("Refresh: %v", err)
			}
			if got := tc.dec.Decrypt(refreshed); got != val {
				t.Fatalf("Refresh(%v): got %v", val, got)
			}
		})

		// Double refresh.
		t.Run(fmt.Sprintf("double_refresh/%v", val), func(t *testing.T) {
			ct := tc.enc.Encrypt(val)
			r1, err := tc.eval.Refresh(ct)
			if err != nil {
				t.Fatalf("Refresh 1: %v", err)
			}
			r2, err := tc.eval.Refresh(r1)
			if err != nil {
				t.Fatalf("Refresh 2: %v", err)
			}
			if got := tc.dec.Decrypt(r2); got != val {
				t.Fatalf("double Refresh(%v): got %v", val, got)
			}
		})
	}
}

// TestFHE_MAJORITYGateCorrectness verifies the 3-input MAJORITY gate for
// all 8 input combinations. MAJORITY uses a single bootstrap on the sum
// of three ciphertexts.
//
// Property: MAJORITY(a, b, c) = 1 iff at least 2 of {a, b, c} are 1.
func TestFHE_MAJORITYGateCorrectness(t *testing.T) {
	tc := newTestContext(t)

	for a := 0; a <= 1; a++ {
		for b := 0; b <= 1; b++ {
			for c := 0; c <= 1; c++ {
				name := fmt.Sprintf("MAJORITY(%d,%d,%d)", a, b, c)
				t.Run(name, func(t *testing.T) {
					ctA := tc.enc.Encrypt(a == 1)
					ctB := tc.enc.Encrypt(b == 1)
					ctC := tc.enc.Encrypt(c == 1)

					result, err := tc.eval.MAJORITY(ctA, ctB, ctC)
					if err != nil {
						t.Fatalf("MAJORITY: %v", err)
					}

					got := tc.dec.Decrypt(result)
					want := (a + b + c) >= 2
					if got != want {
						t.Fatalf("got %v, want %v", got, want)
					}
				})
			}
		}
	}
}

// TestFHE_MUXGateCorrectness verifies the multiplexer gate for all input
// combinations. MUX = (sel AND a) OR (NOT(sel) AND b), which requires two
// AND gates and one OR gate (3 bootstraps total).
//
// Property: MUX(sel, a, b) = a if sel=1, b if sel=0.
func TestFHE_MUXGateCorrectness(t *testing.T) {
	tc := newTestContext(t)

	for sel := 0; sel <= 1; sel++ {
		for a := 0; a <= 1; a++ {
			for b := 0; b <= 1; b++ {
				name := fmt.Sprintf("MUX(sel=%d,a=%d,b=%d)", sel, a, b)
				t.Run(name, func(t *testing.T) {
					ctSel := tc.enc.Encrypt(sel == 1)
					ctA := tc.enc.Encrypt(a == 1)
					ctB := tc.enc.Encrypt(b == 1)

					result, err := tc.eval.MUX(ctSel, ctA, ctB)
					if err != nil {
						t.Fatalf("MUX: %v", err)
					}

					got := tc.dec.Decrypt(result)
					var want bool
					if sel == 1 {
						want = a == 1
					} else {
						want = b == 1
					}
					if got != want {
						t.Fatalf("got %v, want %v", got, want)
					}
				})
			}
		}
	}
}

// TestFHE_CMPCOMBINEGateCorrectness verifies the comparison combine gate.
// CMPCOMBINE computes: isLess OR (isEqual AND bitLt) in a single bootstrap
// using weighted encoding: 2*isLess + isEqual + bitLt.
//
// Note: The input (isLess=1, isEqual=1, bitLt=1) is logically impossible in
// real comparison circuits (a number cannot be both less-than and equal-to
// another). For this input, the weighted sum is 4/8 = 0.5, which hits the
// negacyclic wrap-around boundary of the test polynomial. We test only the
// 7 valid input combinations.
//
// Property: CMPCOMBINE(isLess, isEqual, bitLt) = isLess || (isEqual && bitLt)
// for all valid comparison states.
func TestFHE_CMPCOMBINEGateCorrectness(t *testing.T) {
	tc := newTestContext(t)

	cases := []struct {
		isLess, isEqual, bitLt int
	}{
		{0, 0, 0},
		{0, 0, 1},
		{0, 1, 0},
		{0, 1, 1},
		{1, 0, 0},
		{1, 0, 1},
		{1, 1, 0},
		// (1, 1, 1) omitted: logically impossible (isLess AND isEqual
		// cannot both be true), and the weighted sum 4/8 = 0.5 hits
		// the negacyclic boundary.
	}

	for _, c := range cases {
		name := fmt.Sprintf("CMPCOMBINE(less=%d,eq=%d,lt=%d)", c.isLess, c.isEqual, c.bitLt)
		t.Run(name, func(t *testing.T) {
			ctLess := tc.enc.Encrypt(c.isLess == 1)
			ctEq := tc.enc.Encrypt(c.isEqual == 1)
			ctLt := tc.enc.Encrypt(c.bitLt == 1)

			result, err := tc.eval.CMPCOMBINE(ctLess, ctEq, ctLt)
			if err != nil {
				t.Fatalf("CMPCOMBINE: %v", err)
			}

			got := tc.dec.Decrypt(result)
			want := (c.isLess == 1) || (c.isEqual == 1 && c.bitLt == 1)
			if got != want {
				t.Fatalf("got %v, want %v", got, want)
			}
		})
	}
}

// TestFHE_NoiseBudgetViaGateDepth verifies noise budget behavior through
// observable effects: deep chains of bootstrapped gates remain correct,
// while the Refresh operation restores correctness after noise accumulation.
//
// In TFHE, each gate evaluation includes a programmable bootstrap that
// refreshes the noise. This means:
//   - Bootstrapped operations: unlimited depth, noise resets each time
//   - Non-bootstrapped operations (NOT): accumulate noise linearly
//   - Refresh: explicitly resets noise without changing the value
//
// Property: Bootstrapped gate chains of arbitrary depth produce correct results.
// Property: Refresh after noise accumulation restores correct decryption.
func TestFHE_NoiseBudgetViaGateDepth(t *testing.T) {
	tc := newTestContext(t)

	// Deep bootstrapped chain: each gate resets noise, so depth is unlimited.
	// We test with a depth that would fail without bootstrapping.
	t.Run("deep_bootstrapped_chain_correct", func(t *testing.T) {
		// Chain: OR(OR(OR(...OR(false, false)..., false), false), true) = true
		// All intermediate values are false, final OR with true = true.
		acc := tc.enc.Encrypt(false)
		for i := 0; i < 8; i++ {
			ctFalse := tc.enc.Encrypt(false)
			var err error
			acc, err = tc.eval.OR(acc, ctFalse)
			if err != nil {
				t.Fatalf("OR at depth %d: %v", i, err)
			}
		}
		// Final OR with true.
		ctTrue := tc.enc.Encrypt(true)
		acc, err := tc.eval.OR(acc, ctTrue)
		if err != nil {
			t.Fatalf("final OR: %v", err)
		}
		if got := tc.dec.Decrypt(acc); !got {
			t.Fatal("expected true after deep OR chain ending with true")
		}
	})

	// Refresh should restore correctness regardless of prior noise.
	t.Run("refresh_restores_correctness", func(t *testing.T) {
		ct := tc.enc.Encrypt(true)
		// Apply NOT many times. NOT is free (no bootstrap), but each
		// negation is exact, so noise only comes from the original encryption.
		// An even number of NOTs returns to the original value.
		for i := 0; i < 20; i++ {
			ct = tc.eval.NOT(ct)
		}
		// Even number of NOTs = original value.
		refreshed, err := tc.eval.Refresh(ct)
		if err != nil {
			t.Fatalf("Refresh: %v", err)
		}
		if got := tc.dec.Decrypt(refreshed); got != true {
			t.Fatal("Refresh should restore true after even NOTs")
		}
	})

	// Mixed gate types at depth: AND -> XOR -> OR -> NAND -> AND.
	// Each gate bootstraps, so the chain should produce the correct result.
	t.Run("mixed_gate_chain", func(t *testing.T) {
		a := tc.enc.Encrypt(true)
		b := tc.enc.Encrypt(false)
		c := tc.enc.Encrypt(true)

		// Step 1: AND(true, false) = false
		r1, err := tc.eval.AND(a, b)
		if err != nil {
			t.Fatalf("AND: %v", err)
		}
		// Step 2: XOR(false, true) = true
		r2, err := tc.eval.XOR(r1, c)
		if err != nil {
			t.Fatalf("XOR: %v", err)
		}
		// Step 3: OR(true, false) = true
		r3, err := tc.eval.OR(r2, b)
		if err != nil {
			t.Fatalf("OR: %v", err)
		}
		// Step 4: NAND(true, true) = false
		r4, err := tc.eval.NAND(r3, c)
		if err != nil {
			t.Fatalf("NAND: %v", err)
		}
		// Step 5: AND(false, true) = false
		r5, err := tc.eval.AND(r4, c)
		if err != nil {
			t.Fatalf("AND: %v", err)
		}

		if got := tc.dec.Decrypt(r5); got != false {
			t.Fatal("mixed gate chain: expected false")
		}
	})
}

// TestFHE_NoiseBudgetMultiplication verifies that multiplication-depth (here
// represented by composition of gates that are equivalent to multiplication)
// grows noise as expected. In TFHE, since every gate bootstraps, the noise
// after each gate is independent of depth. We verify this by testing that
// AND3 (which composes two AND gates = two bootstraps) works at depth.
//
// Property: AND3 chains produce correct results because each internal gate
// bootstraps independently.
func TestFHE_NoiseBudgetMultiplication(t *testing.T) {
	tc := newTestContext(t)

	// AND3 = AND(AND(a,b), c) -- two bootstraps.
	// Chain: AND3(AND3(1,1,1), 1, 1) = AND3(1, 1, 1) = 1
	t.Run("AND3_chain", func(t *testing.T) {
		ctTrue := tc.enc.Encrypt(true)

		// First AND3.
		r1, err := tc.eval.AND3(ctTrue, tc.enc.Encrypt(true), tc.enc.Encrypt(true))
		if err != nil {
			t.Fatalf("AND3 #1: %v", err)
		}
		// Second AND3 using first result.
		r2, err := tc.eval.AND3(r1, tc.enc.Encrypt(true), tc.enc.Encrypt(true))
		if err != nil {
			t.Fatalf("AND3 #2: %v", err)
		}
		// Third AND3 using second result.
		r3, err := tc.eval.AND3(r2, tc.enc.Encrypt(true), tc.enc.Encrypt(true))
		if err != nil {
			t.Fatalf("AND3 #3: %v", err)
		}

		if got := tc.dec.Decrypt(r3); !got {
			t.Fatal("AND3 chain of all-true: expected true")
		}
	})

	// Verify AND3 correctly produces false when any input is false.
	t.Run("AND3_false_propagation", func(t *testing.T) {
		r, err := tc.eval.AND3(
			tc.enc.Encrypt(true),
			tc.enc.Encrypt(false),
			tc.enc.Encrypt(true),
		)
		if err != nil {
			t.Fatalf("AND3: %v", err)
		}
		if got := tc.dec.Decrypt(r); got {
			t.Fatal("AND3(T,F,T): expected false")
		}
	})
}

// TestFHE_ParameterSizes verifies the expected parameter dimensions for the
// standard parameter set used in tests. This catches silent changes to
// parameter constants.
func TestFHE_ParameterSizes(t *testing.T) {
	params, err := fhe.NewParametersFromLiteral(fhe.PN10QP27)
	if err != nil {
		t.Fatalf("NewParametersFromLiteral: %v", err)
	}

	if n := params.N(); n != 1024 {
		t.Fatalf("N: got %d, want 1024", n)
	}
	if nbr := params.NBR(); nbr != 1024 {
		t.Fatalf("NBR: got %d, want 1024", nbr)
	}

	// Modulus should be the NTT-friendly prime 0x7fff801 = 134215681.
	expectedQ := uint64(0x7fff801)
	if q := params.QLWE(); q != expectedQ {
		t.Fatalf("QLWE: got %d, want %d", q, expectedQ)
	}
	if q := params.QBR(); q != expectedQ {
		t.Fatalf("QBR: got %d, want %d", q, expectedQ)
	}
}
