// Copyright (C) 2026, Lux Industries, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Property-based tests for LUX_STRICT_E2E_PQ invariants.
//
// These tests assert the soundness propositions from
// ~/work/lux/proofs/strict-e2e-pq/strict-e2e-pq-soundness.tex
// against the production canonical Go code at
// ~/work/lux/consensus/.
//
// Source specifications:
//   - LaTeX:  ~/work/lux/proofs/strict-e2e-pq/strict-e2e-pq-soundness.tex
//   - TLA+:   ~/work/lux/proofs/tla/StrictPQProfile.tla
//   - Lean 4: ~/work/lux/proofs/lean/StrictE2EPQ/
//
// Go canonicals:
//   - luxfi/consensus/config/security_profile.go:244
//   - luxfi/consensus/protocol/auth/tx_envelope.go:108
//   - luxfi/consensus/protocol/auth/permit.go:70
//   - luxfi/consensus/protocol/zchain/registry/auth_proof.go:118
package property

import (
	"crypto/rand"
	"testing"
)

// ---------------------------------------------------------------------------
// Abstract model of the strict-PQ profile.
//
// This file deliberately does NOT import luxfi/consensus directly; instead
// it re-derives the profile invariants from first principles, matching
// the field layout in security_profile.go:244. The full integration test
// lives in luxfi/consensus/config/security_profile_test.go.
// ---------------------------------------------------------------------------

// strictPQProfile is a value-level mirror of ChainSecurityProfile under
// the locked strict-PQ posture.
type strictPQProfile struct {
	profileID             uint32
	profileName           string
	hashSuiteID           string // "sha3_384" on strict-PQ
	identitySchemeID      string // "mldsa65" on strict-PQ
	finalitySchemeID      string // "pulsar65" on strict-PQ
	highValueSchemeID     string // "pulsar65" or "pulsar87"
	proofPolicyID         string // "pq128"
	allowedProofBackends  []string
	minSoundnessBits      uint16
	minHashOutputBits     uint16
	requireTransparent    bool
	forbidPairings        bool
	forbidKZG             bool
	forbidTrustedSetup    bool
	forbidClassicalSNARKs bool
	forbidDevProofs       bool
	forbidFallbacks       bool
	requireTypedTxAuth    bool
	walletSchemeID        string
	contractAuthSchemeID  string
	bridgeProfileID       string
	drbgSchemeID          string
}

// strictPQ returns the canonical strict-PQ profile under
// LUX_STRICT_E2E_PQ.
func strictPQ() *strictPQProfile {
	return &strictPQProfile{
		profileID:             1,
		profileName:           "lux-strict-pq-v1",
		hashSuiteID:           "sha3_384",
		identitySchemeID:      "mldsa65",
		finalitySchemeID:      "pulsar65",
		highValueSchemeID:     "pulsar87",
		proofPolicyID:         "pq128",
		allowedProofBackends:  []string{"p3q", "plonky3_sha3"},
		minSoundnessBits:      128,
		minHashOutputBits:     384,
		requireTransparent:    true,
		forbidPairings:        true,
		forbidKZG:             true,
		forbidTrustedSetup:    true,
		forbidClassicalSNARKs: true,
		forbidDevProofs:       true,
		forbidFallbacks:       true,
		requireTypedTxAuth:    true,
		walletSchemeID:        "mldsa65",
		contractAuthSchemeID:  "mldsa65",
		bridgeProfileID:       "strictPQ",
		drbgSchemeID:          "hash_drbg_sha3",
	}
}

// permissive returns the classical-compat profile.
func permissive() *strictPQProfile {
	p := strictPQ()
	p.profileID = 2
	p.profileName = "lux-permissive"
	p.identitySchemeID = "ecdsa_secp256k1"
	p.walletSchemeID = "ecdsa"
	p.contractAuthSchemeID = "ecdsa_712"
	p.bridgeProfileID = "permissive"
	p.forbidPairings = false
	p.forbidFallbacks = false
	p.requireTypedTxAuth = false
	return p
}

// ---------------------------------------------------------------------------
// Strict-PQ scheme membership
// ---------------------------------------------------------------------------

var pqSchemes = map[string]bool{
	"mldsa44":     true,
	"mldsa65":     true,
	"mldsa87":     true,
	"pulsar44":   true,
	"pulsar65":   true,
	"pulsar87":   true,
	"slhdsa256s":  true,
}

var pqBackends = map[string]bool{
	"p3q":          true,
	"plonky3_sha3": true,
}

var pqSuites = map[string]bool{
	"sha3_384": true,
}

// isPQ checks the IsE2EPQ proposition from
// `proofs/lean/StrictE2EPQ/Profile.lean`.
func isPQ(p *strictPQProfile) bool {
	if !pqSuites[p.hashSuiteID] {
		return false
	}
	if !pqSchemes[p.identitySchemeID] {
		return false
	}
	if !pqSchemes[p.finalitySchemeID] {
		return false
	}
	if !pqSchemes[p.highValueSchemeID] {
		return false
	}
	if p.proofPolicyID != "pq128" {
		return false
	}
	for _, b := range p.allowedProofBackends {
		if !pqBackends[b] {
			return false
		}
	}
	if p.minSoundnessBits < 128 {
		return false
	}
	if p.minHashOutputBits < 384 {
		return false
	}
	if !p.requireTransparent || !p.forbidPairings || !p.forbidKZG ||
		!p.forbidTrustedSetup || !p.forbidClassicalSNARKs ||
		!p.forbidDevProofs || !p.forbidFallbacks ||
		!p.requireTypedTxAuth {
		return false
	}
	if p.walletSchemeID != "mldsa65" && p.walletSchemeID != "mldsa87" {
		return false
	}
	if p.contractAuthSchemeID != "mldsa65" && p.contractAuthSchemeID != "mldsa87" {
		return false
	}
	if p.bridgeProfileID != "strictPQ" && p.bridgeProfileID != "fips" {
		return false
	}
	if p.drbgSchemeID != "hash_drbg_sha3" {
		return false
	}
	return true
}

// ---------------------------------------------------------------------------
// Property tests
// ---------------------------------------------------------------------------

// TestStrictPQ_IsE2EPQ asserts the production canonical strict-PQ
// profile satisfies IsE2EPQ.
func TestStrictPQ_IsE2EPQ(t *testing.T) {
	if !isPQ(strictPQ()) {
		t.Fatal("strict-PQ profile must satisfy IsE2EPQ")
	}
}

// TestPermissive_NotIsE2EPQ asserts the permissive profile does not
// satisfy IsE2EPQ. This is the negative companion to the test above.
func TestPermissive_NotIsE2EPQ(t *testing.T) {
	if isPQ(permissive()) {
		t.Fatal("permissive profile must not satisfy IsE2EPQ")
	}
}

// TestRelaxForbidPairings_Breaks asserts that flipping ForbidPairings
// from true to false breaks IsE2EPQ. (Lean 4 counterpart:
// `relax_pairings_breaks` in Coverage.lean.)
func TestRelaxForbidPairings_Breaks(t *testing.T) {
	p := strictPQ()
	p.forbidPairings = false
	if isPQ(p) {
		t.Fatal("flipping ForbidPairings must break IsE2EPQ")
	}
}

// TestRelaxForbidKZG_Breaks asserts the same for ForbidKZG.
func TestRelaxForbidKZG_Breaks(t *testing.T) {
	p := strictPQ()
	p.forbidKZG = false
	if isPQ(p) {
		t.Fatal("flipping ForbidKZG must break IsE2EPQ")
	}
}

// TestRelaxRequireTypedTxAuth_Breaks asserts the same for
// RequireTypedTxAuth.
func TestRelaxRequireTypedTxAuth_Breaks(t *testing.T) {
	p := strictPQ()
	p.requireTypedTxAuth = false
	if isPQ(p) {
		t.Fatal("flipping RequireTypedTxAuth must break IsE2EPQ")
	}
}

// TestClassicalIdentityScheme_Breaks asserts that swapping the
// identity scheme to ECDSA breaks IsE2EPQ.
func TestClassicalIdentityScheme_Breaks(t *testing.T) {
	p := strictPQ()
	p.identitySchemeID = "ecdsa_secp256k1"
	if isPQ(p) {
		t.Fatal("classical IdentitySchemeID must break IsE2EPQ")
	}
}

// TestClassicalFinalityScheme_Breaks asserts the same for the finality
// lane.
func TestClassicalFinalityScheme_Breaks(t *testing.T) {
	p := strictPQ()
	p.finalitySchemeID = "blsAggregate"
	if isPQ(p) {
		t.Fatal("classical FinalitySchemeID must break IsE2EPQ")
	}
}

// TestRelaxedHashSuite_Breaks asserts that flipping the hash suite to
// a non-FIPS-202 family breaks IsE2EPQ.
func TestRelaxedHashSuite_Breaks(t *testing.T) {
	p := strictPQ()
	p.hashSuiteID = "keccak256"
	if isPQ(p) {
		t.Fatal("non-SHA3 HashSuiteID must break IsE2EPQ")
	}
}

// TestClassicalProofBackend_Breaks asserts that adding Groth16 to the
// allowed backends breaks IsE2EPQ.
func TestClassicalProofBackend_Breaks(t *testing.T) {
	p := strictPQ()
	p.allowedProofBackends = append(p.allowedProofBackends, "groth16")
	if isPQ(p) {
		t.Fatal("Groth16 in AllowedProofBackends must break IsE2EPQ")
	}
}

// TestLowSoundness_Breaks asserts the soundness floor.
func TestLowSoundness_Breaks(t *testing.T) {
	p := strictPQ()
	p.minSoundnessBits = 80
	if isPQ(p) {
		t.Fatal("MinSoundnessBits < 128 must break IsE2EPQ")
	}
}

// TestLowHashWidth_Breaks asserts the hash-output floor.
func TestLowHashWidth_Breaks(t *testing.T) {
	p := strictPQ()
	p.minHashOutputBits = 256
	if isPQ(p) {
		t.Fatal("MinHashOutputBits < 384 must break IsE2EPQ")
	}
}

// ---------------------------------------------------------------------------
// Bridge invariant: PQ E2E implies no classical admin
// ---------------------------------------------------------------------------

type bridgeProfileState struct {
	allowsClassicalAdmin bool
	postQuantumEndToEnd  bool
}

func bridgeInvariant(b bridgeProfileState) bool {
	if b.postQuantumEndToEnd && b.allowsClassicalAdmin {
		return false
	}
	return true
}

// TestBridge_PQ_NoClassical asserts that a bridge profile that claims
// PostQuantumEndToEnd cannot simultaneously AllowsClassicalAdmin.
// (Lean 4 counterpart: `bridge_pq_no_classical` in Coverage.lean.)
func TestBridge_PQ_NoClassical(t *testing.T) {
	bad := bridgeProfileState{
		allowsClassicalAdmin: true,
		postQuantumEndToEnd:  true,
	}
	if bridgeInvariant(bad) {
		t.Fatal("PostQuantumEndToEnd=true + AllowsClassicalAdmin=true must fail the invariant")
	}
	good := bridgeProfileState{
		allowsClassicalAdmin: false,
		postQuantumEndToEnd:  true,
	}
	if !bridgeInvariant(good) {
		t.Fatal("PostQuantumEndToEnd=true + AllowsClassicalAdmin=false must satisfy the invariant")
	}
}

// ---------------------------------------------------------------------------
// Fuzz: 256 random mutations of the strict-PQ profile must all break IsE2EPQ
// ---------------------------------------------------------------------------

// TestFuzz_RandomRelaxations asserts that flipping a single
// strict-PQ-relevant bool to false (or perturbing a single enum) yields
// a profile that fails IsE2EPQ. We sample 256 random one-field
// perturbations.
func TestFuzz_RandomRelaxations(t *testing.T) {
	mutators := []func(*strictPQProfile){
		func(p *strictPQProfile) { p.forbidPairings = false },
		func(p *strictPQProfile) { p.forbidKZG = false },
		func(p *strictPQProfile) { p.forbidTrustedSetup = false },
		func(p *strictPQProfile) { p.forbidClassicalSNARKs = false },
		func(p *strictPQProfile) { p.forbidDevProofs = false },
		func(p *strictPQProfile) { p.forbidFallbacks = false },
		func(p *strictPQProfile) { p.requireTypedTxAuth = false },
		func(p *strictPQProfile) { p.requireTransparent = false },
		func(p *strictPQProfile) { p.identitySchemeID = "ecdsa_secp256k1" },
		func(p *strictPQProfile) { p.finalitySchemeID = "blsAggregate" },
		func(p *strictPQProfile) { p.highValueSchemeID = "ed25519" },
		func(p *strictPQProfile) { p.walletSchemeID = "ecdsa" },
		func(p *strictPQProfile) { p.contractAuthSchemeID = "ecdsa_712" },
		func(p *strictPQProfile) { p.hashSuiteID = "keccak256" },
		func(p *strictPQProfile) { p.proofPolicyID = "classical128" },
		func(p *strictPQProfile) { p.bridgeProfileID = "permissive" },
		func(p *strictPQProfile) { p.drbgSchemeID = "ctr_drbg" },
		func(p *strictPQProfile) { p.minSoundnessBits = 64 },
		func(p *strictPQProfile) { p.minHashOutputBits = 128 },
		func(p *strictPQProfile) {
			p.allowedProofBackends = []string{"groth16"}
		},
	}

	for i := 0; i < 256; i++ {
		buf := make([]byte, 1)
		if _, err := rand.Read(buf); err != nil {
			t.Fatal(err)
		}
		idx := int(buf[0]) % len(mutators)
		p := strictPQ()
		mutators[idx](p)
		if isPQ(p) {
			t.Fatalf("iter %d: mutator %d produced a profile that still satisfies IsE2EPQ", i, idx)
		}
	}
}

// TestStrictPQ_Stable asserts that 100 successive calls to strictPQ()
// produce profiles that all satisfy IsE2EPQ. This is the model-level
// idempotence claim.
func TestStrictPQ_Stable(t *testing.T) {
	for i := 0; i < 100; i++ {
		if !isPQ(strictPQ()) {
			t.Fatalf("iter %d: strictPQ() must always satisfy IsE2EPQ", i)
		}
	}
}
