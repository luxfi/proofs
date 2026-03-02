# Lux Formal Verification

Machine-checked proofs for the Lux consensus stack and Solidity contract invariants.

## Structure

- `lean/` — Lean4 proofs (consensus, crypto, DeFi, network, storage, trust)
- `tla/` — TLA+ specifications
- `tamarin/` — Tamarin protocol verification
- `halmos/` — Halmos symbolic execution for Solidity
- `property/` — Property-based testing

## Key Consensus Proofs (Lean4)

### Quasar Consensus (`lean/Consensus/Quasar.lean`)
Proves the composition of three independent cryptographic hardness assumptions:
- **BLS12-381** (ECDL, classical)
- **Ringtail Ring-LWE** (Module-LWE, post-quantum)
- **ML-DSA-65 FIPS 204** (Module-LWE + Module-SIS, post-quantum)

Theorems:
- `triple_requires_all`: all three layers must reach quorum
- `quantum_safe_triple`: BLS compromise does not affect PQ layers
- `independent_pq_from_classical`: PQ quorum holds regardless of BLS state
- `triple_implies_dual_*`: triple mode subsumes all dual modes
- `cert_intersection`: two valid certs share honest signers (BFT)
- `unique_per_round`: at most one value certified per round

Four modes: BLS-only, BLS+ML-DSA, BLS+Ringtail, BLS+Ringtail+ML-DSA (triple).

### Crypto Proofs (`lean/Crypto/`)
- `BLS.lean` — BLS12-381 aggregate signature unforgeability
- `MLDSA.lean` — ML-DSA-65 (FIPS 204) correctness
- `Ringtail.lean` — Ring-LWE threshold signature security
- `Hybrid.lean` — Triple hybrid identity sig (Ed25519 + ML-DSA + SLH-DSA)
- `MLKEM.lean` — ML-KEM-768 key encapsulation
- `FROST.lean` — FROST threshold signing
- `Threshold/` — General threshold signature proofs

### BFT Safety (`lean/Consensus/`)
- `Safety.lean` — no two conflicting finalized values
- `Liveness.lean` — progress under partial synchrony
- `Finality.lean` — finalized values are permanent
- `BFT.lean` — quorum intersection (2f+1 of 3f+1)
- `ThresholdProof.lean` — threshold signature scheme correctness
