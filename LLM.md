# Lux Formal Verification

Lean proof scripts for the Lux consensus stack, plus TLA+, Tamarin and Halmos
artifacts. 115 Lean files: **756 theorems and lemmas, 503 axioms, 0 `sorry`**.

`lake build` runs in CI (`.hanzo/workflows/proofs.yml`) over every library the
lakefile declares, so Lean checks the corpus on every push. Say "checked"
precisely: Lean confirms each proof follows from what it is given, and 503 of
those givens are axioms. 55 declarations state `True`, which `trivial` proves,
so they assume nothing and establish nothing — `lean/vacuity.py` lists them and
CI prints the count next to the build that cannot see them.

Ten modules are in no library and are never compiled, among them
`Crypto/Corona/Unforgeability.lean` and `Main.lean`. CI prints that list too,
derived from the build's own output rather than from the lakefile.

Read the file before calling a result proved. Several headline theorems are
short compositions of axioms declared directly above them and say so in their
own comments.

## Post-E2E-PQ State (current)

Lean 4 + Tamarin + Halmos artifacts back the post-E2E-PQ proposal set.
Quasar soundness, Pulsar-M output-interchangeability, and Z-Chain key
registry safety are the three active proof tracks.

### Recent significant commits

| SHA | Impact |
|-----|--------|
| `07d01da` | Remove downstream-tenant branding cross-contamination |
| `ef3c3df` | M/F/Z-Chain canonical naming per LP-134 |
| `aaee863` | Scrub Avalabs IP brand refs |
| `c5d805f` | Lux liquidity protocol adoption + Quasar refs + Pulsar naming |
| `562beb9` | Fix Lean 4.14 / Mathlib v4.14 compatibility in DAG consensus proofs |
| `c29e738` | `sequential_worldview_preserved` proved (was axiom) |
| `0e20c6d` | DAG-EVM, DAG-Z-Chain, PQZ parallelism, TLA+ specs, Tamarin, Halmos, property tests |

### Active proof tracks

Axiom and theorem counts are per file, measured. A track resting on axioms is
not thereby wrong — cryptographic hardness has to be assumed somewhere — but the
count is what separates an assumption from a result, so it is the status.

| Track | File | ax | thm | Status |
|-------|------|---:|----:|--------|
| BFT quorum intersection | `lean/Consensus/BFT.lean` | 0 | 5 | Proved, no axioms |
| Quasar modes | `lean/Consensus/Quasar.lean` | 0 | 11 | Proved, no axioms |
| ML-DSA boundary clearance | `lean/Crypto/Pulsar/BoundaryClearance.lean` | 1 | 16 | Proved; real hint arithmetic |
| Shamir scaling | `lean/Crypto/Pulsar/Shamir.lean` | 1 | 5 | Proved (algebraic) + empirical (Go tests) |
| Quasar triple defence | `lean/Quasar/Consensus.lean` | 4 | 14 | Modus tollens against 4 hardness axioms |
| Pulsar unforgeability (TS-UF) | `lean/Crypto/Pulsar/Unforgeability.lean` | 3 | 6 | Reduction stated; `TSUFBound` is defined as `True` |
| Pulsar output-interchangeability | `lean/Crypto/Pulsar/OutputInterchange.lean` | 2 | 1 | Reduction stated |
| DAG-EVM safety | `lean/Consensus/Safety.lean` | 3 | 2 | `safety` composes two axioms; the proved window lemma beside it is unused |
| Liveness | `lean/Consensus/Liveness.lean` | 10 | 1 | The theorem applies the axioms that are the argument |
| Corona unforgeability | `lean/Crypto/Corona/Unforgeability.lean` | — | — | In no library; never compiled |
| Z-Chain key registry safety | TBD (HIP-0078 §4) | — | — | Open |

The three `lean/Crypto/Pulsar_M/…` paths this table used to cite do not exist;
the files are under `lean/Crypto/Pulsar/`.

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
Proves the composition of independent cryptographic hardness assumptions
across two families (lattice + pairing):
- **BLS12-381** (ECDL, classical)
- **Corona** (Module-LWE + Module-SIS, eprint 2024/1113, post-quantum;
  Lux fork of Ringtail — module dims M=8/N=7, q=0x1000000004A01 48-bit,
  σ_E=6.108, NIST Cat-1; same lattice family as Pulsar, distinct
  parameter regime / lifecycle)
- **Pulsar / ML-DSA-65 FIPS 204** (Module-LWE + Module-SIS, post-quantum)

Note: Corona and Pulsar/ML-DSA are BOTH Module-LWE — their diversity is
parameter-regime / codebase, not family-disjoint. Magnetar (SLH-DSA /
hash) is the only true cross-family signature leg.

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
- `Corona.lean` — Module-LWE threshold signature security (Ringtail fork)
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
