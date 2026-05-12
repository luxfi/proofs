# Lux Formal Verification

Machine-checked proofs for the Lux consensus stack and Solidity contract invariants.

## Post-E2E-PQ State (current)

Lean 4 + Tamarin + Halmos artifacts back the post-E2E-PQ proposal set.
Quasar soundness, Pulsar-M output-interchangeability, and Z-Chain key
registry safety are the three active proof tracks.

### Recent significant commits

| SHA | Impact |
|-----|--------|
| `07d01da` | Remove Liquidity branding cross-contamination |
| `ef3c3df` | M/F/Z-Chain canonical naming per LP-134 |
| `aaee863` | Scrub Avalabs IP brand refs |
| `c5d805f` | Lux liquidity protocol adoption + Quasar refs + Pulsar naming |
| `562beb9` | Fix Lean 4.14 / Mathlib v4.14 compatibility in DAG consensus proofs |
| `c29e738` | `sequential_worldview_preserved` proved (was axiom) |
| `0e20c6d` | DAG-EVM, DAG-Z-Chain, PQZ parallelism, TLA+ specs, Tamarin, Halmos, property tests |

### Active proof tracks

| Track | Files | Status |
|-------|-------|--------|
| Quasar soundness | `lean/Consensus/Quasar.lean` + `~/work/lux/papers/lp-020-quasar-consensus.tex` Thm 7.5 | Proved |
| Pulsar-M unforgeability (TS-UF) | `pulsar-m/unforgeability.tex` + `lean/Crypto/Pulsar_M/Unforgeability.lean` | Reduction stated, mechanization in flight |
| Pulsar-M output-interchangeability (Class N1) | `pulsar-m/output-interchangeability.tex` + `lean/Crypto/Pulsar_M/OutputInterchange.lean` | Reduction stated, mechanization in flight |
| Pulsar-M Shamir scaling to N=1,111,111 | `pulsar-m/scaling.tex` + `lean/Crypto/Pulsar_M/Shamir.lean` | Proved (algebraic) + empirical (Go tests) |
| Pulsar-M DKG soundness + privacy | `pulsar-m/dkg-soundness.tex` | Reduction stated |
| Pulsar-M reshare pk-invariance + soundness + privacy | `pulsar-m/reshare-preservation.tex` | Reduction stated |
| Z-Chain key registry safety | TBD (HIP-0078 §4) | Open |
| DAG-EVM safety | `lean/Consensus/Safety.lean` | Proved |
| BFT quorum intersection | `lean/Consensus/BFT.lean` | Proved |

### Cross-repo coherence
- `lean/` tracks `~/work/lux/papers/` theorem numbers 1:1.
- `tamarin/` mirrors the auth-permit protocol from
  `luxfi/consensus/protocol/auth/permit.go`.
- `halmos/` mirrors invariants on `luxfi/contracts/src/pqauth/`.

---

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
- **Corona Ring-LWE** (Module-LWE, post-quantum)
- **ML-DSA-65 FIPS 204** (Module-LWE + Module-SIS, post-quantum)

Theorems:
- `triple_requires_all`: all three layers must reach quorum
- `quantum_safe_triple`: BLS compromise does not affect PQ layers
- `independent_pq_from_classical`: PQ quorum holds regardless of BLS state
- `triple_implies_dual_*`: triple mode subsumes all dual modes
- `cert_intersection`: two valid certs share honest signers (BFT)
- `unique_per_round`: at most one value certified per round

Four modes: BLS-only, BLS+ML-DSA, BLS+Corona, BLS+Corona+ML-DSA (triple).

### Crypto Proofs (`lean/Crypto/`)
- `BLS.lean` — BLS12-381 aggregate signature unforgeability
- `MLDSA.lean` — ML-DSA-65 (FIPS 204) correctness
- `Corona.lean` — Ring-LWE threshold signature security
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
