# Lux Formal Verification

Lean proof scripts for the Lux consensus stack, plus TLA+, Tamarin and Halmos
artifacts. 116 Lean files: **760 theorems and lemmas, 504 axioms, 0 `sorry`**.

`lake build` runs in CI (`.hanzo/workflows/proofs.yml`) over every library the
lakefile declares. Lean confirms each proof follows from what it is given; 504
of those givens are axioms.

Four numbers CI prints on every run, because none is visible in a green build:

- **594 of 715 theorems are proved outright.** `lean/axioms.py` runs
  `#print axioms` over the corpus. Lean's own `propext`, `Classical.choice` and
  `Quot.sound` are the ambient logic rather than assumptions about our systems,
  so a theorem resting on those alone is proved and anything else it names is
  load-bearing. The remaining 121 are conditional, and the report ranks the
  axioms by how many theorems stand on them — which is where the corpus's
  weight actually sits.
- **504 axioms.** Cryptographic hardness must be assumed somewhere, so an axiom
  is not a defect. The count is what separates an assumption from a result.
- **75 declarations carry no content.** `lean/vacuity.py` names three ways a
  statement can be empty and lists every instance: it `states True`, which
  `trivial` proves; it `is provable by rfl`, as `∃ x, e = x` is; or it
  `restates a hypothesis`.
- **10 modules are in no library** and so are never compiled, among them
  `Crypto/Corona/Unforgeability.lean` and `Main.lean`. The list comes from the
  build's own output: a source file with no `.olean` was not checked.

Read the file before calling a result proved. Several headline theorems are
short compositions of axioms declared directly above them, and say so in their
own comments.

## Active proof tracks

Axiom and theorem counts are per file, measured. A track resting on axioms is
not thereby wrong — cryptographic hardness has to be assumed somewhere — but the
count is what separates an assumption from a result, so it is the status.

| Track | File | ax | thm | Status |
|-------|------|---:|----:|--------|
| BFT quorum intersection | `lean/Consensus/BFT.lean` | 0 | 5 | Proved, no axioms |
| Quasar modes | `lean/Consensus/Quasar.lean` | 0 | 11 | Proved, no axioms |
| ML-DSA boundary clearance | `lean/Crypto/Pulsar/BoundaryClearance.lean` | 1 | 16 | Proved; real hint arithmetic |
| Shamir scaling | `lean/Crypto/Pulsar/Shamir.lean` | 1 | 5 | Proved (algebraic) + empirical (Go tests) |
| Quasar triple defence | `lean/Quasar/Consensus.lean` | 7 | 17 | Modus tollens against 3 hardness axioms, relative to certificate provenance |
| Strict-PQ profile gate | `lean/StrictE2EPQ/Profile.lean` | 0 | 5 | Proved, no axioms; wire bytes checked against the Go tables, not commented |
| Strict-PQ 14-surface coverage | `lean/StrictE2EPQ/Coverage.lean` | 0 | 27 | Proved, no axioms; decomposition of `IsE2EPQ` |
| Pulsar unforgeability (TS-UF) | `lean/Crypto/Pulsar/Unforgeability.lean` | 3 | 6 | Reduction stated; `TSUFBound` is defined as `True` |
| Pulsar output-interchangeability | `lean/Crypto/Pulsar/OutputInterchange.lean` | 2 | 1 | Reduction stated |
| DAG-EVM safety | `lean/Consensus/Safety.lean` | 3 | 2 | `safety` composes two axioms; the proved window lemma beside it is unused |
| Liveness | `lean/Consensus/Liveness.lean` | 10 | 1 | The theorem applies the axioms that are the argument |
| Corona unforgeability | `lean/Crypto/Corona/Unforgeability.lean` | — | — | In no library; never compiled |
| Z-Chain key registry safety | TBD (HIP-0078 §4) | — | — | Open |

## What the artifacts verify

Each tool checks a *model*, written here, against properties stated here. None
of them reads the production implementation, so agreement between a model and
the code it cites is maintained by hand.

Where a model names a wire constant, it also carries that constant's byte and
proves the value, so `lake build` catches the drift a stale comment hides.
Three `luxfi/consensus` packages declare overlapping scheme-ID tables and they
disagree: `pkg/wire/candidate.go:346-352` assigns Pulsar-M the 0x41/0x42/0x43
bytes that `config/pq_mode.go:305-310` assigns to raw ML-DSA, while requiring
the two tables to be identical; and byte 0x10 is `ContractAuthZChainProof`
(post-quantum) in `config/pq_mode.go:871` and `ContractAuthECDSASecp256k1Legacy`
(classical) in `protocol/auth/scheme_ids.go:202`. `StrictE2EPQ/Profile.lean`
follows `config` and `protocol/auth`, records the divergence on the enums it
affects, and refuses any byte the two readings disagree about. Reconciling the
Go tables is open work in `luxfi/consensus`, not here.

- `lean/` — the models above. Files carry a `Maps to:` block naming the Go,
  Rust or Solidity source they model.
- `tamarin/` — the auth-permit protocol, modelling
  `luxfi/consensus/protocol/auth/permit.go`.
- `halmos/` — Solidity invariants. The harnesses import `forge-std/Test.sol`
  only and re-state the contract logic inline, so they verify the restatement,
  not the deployed contract. `HalmosYieldVault.t.sol` says so in its own header.

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
