# Lux Proofs — INDEX

> Master catalogue of every proof artifact in this repository.
> Complements `README.md` (which gives the high-level inventory + run
> commands). Last regenerated: 2026-05-18.

## Top-level standalone artifacts

| Document | Source | PDF |
|---|---|---|
| Strict-PQ-finality without BLS | `pq-finality-no-bls.tex` | `pq-finality-no-bls.pdf` |
| Quasar certificate soundness | `quasar-cert-soundness.tex` | `quasar-cert-soundness.pdf` |

## LaTeX proof bundles (by topic)

### `pulsar/` — Pulsar threshold ML-DSA (9 documents)

| File | Property |
|---|---|
| `pulsar/activation-safety.tex` | Activation-certificate circuit-breaker correctness |
| `pulsar/dkg-soundness.tex` | DKG soundness (Pedersen-VSS over R_q) |
| `pulsar/grouped-sortition.tex` | Grouped sortition for committee selection |
| `pulsar/hash-suite-separation.tex` | SHAKE / cSHAKE / KMAC domain separation |
| `pulsar/lux-round-metastable.tex` | Lux-round metastability under partial synchrony |
| `pulsar/output-interchangeability.tex` | Byte-equality with FIPS 204 single-party Sign |
| `pulsar/reshare-preservation.tex` | Public-key preservation across resharing |
| `pulsar/scaling.tex` | Per-party cost scaling with committee size |
| `pulsar/unforgeability.tex` | EUF-CMA reduction (high-level) |

The mechanized form (Lean + EasyCrypt) of these claims lives in
`lean/Crypto/Pulsar/` and in `~/work/lux/pulsar/proofs/easycrypt/`.
See `~/work/lux/pulsar/proofs/lean-easycrypt-bridge.md` for the
correspondence map.

### `quasar/` — Quasar consensus (3 documents)

| File | Property |
|---|---|
| `quasar/horizon-soundness.tex` | Horizon finality soundness across DAG |
| `quasar/l1-l2-covalidation.tex` | L1 / L2 co-validation invariants |
| `quasar/warp-pq-soundness.tex` | Warp PQ-messaging soundness |

### `fhe/` — Threshold FHE (4 documents)

| File | Property |
|---|---|
| `fhe/correctness.tex` | TFHE bootstrapping correctness |
| `fhe/dual-runtime-equivalence.tex` | CPU == GPU equivalence on FHE primitives |
| `fhe/nebula-binding.tex` | Nebula chain binding for FHE ciphertexts |
| `fhe/parameter-security.tex` | Parameter selection ↔ NIST cat 3/5 |

### `lss/` — Linear Shamir's Secret Sharing (3 documents)

| File | Property |
|---|---|
| `lss/adapter-contract.tex` | LSS adapter contract for threshold kernels |
| `lss/lifecycle-safety.tex` | Generation / rotation safety |
| `lss/rollback-safety.tex` | RollbackManager invariants |

### `strict-e2e-pq/` — Strict E2E post-quantum profile (1 document)

| File | Property |
|---|---|
| `strict-e2e-pq/strict-e2e-pq-soundness.tex` | End-to-end PQ profile soundness |

### `definitions/` — Shared definitions (3 documents)

| File | Content |
|---|---|
| `definitions/algorithms.tex` | Algorithm definitions used across bundles |
| `definitions/finality-definitions.tex` | Finality predicates |
| `definitions/transcript-binding.tex` | Transcript-binding lemmas |

## Lean 4 (`lean/`)

104 Lean files across 16 top-level subdirectories. Build with
`cd lean && lake build`. The detailed per-subdirectory file list lives
in `README.md`; this section catalogues the directories.

| Subdir | Topic |
|---|---|
| `Bridge/` | Cross-chain bridge invariants |
| `Build/` | Build-system shared lemmas |
| `Compliance/` | Compliance / KYC / sanctions checks |
| `Compute/` | Compute pricing / metering |
| `Consensus/` | Safety, liveness, BFT, Finality, Quasar (11 files) |
| `Crypto/` | Algorithm-level theorems (see below) |
| `DeFi/` | AMM, lending, staking invariants |
| `GPU/` | GPU dispatch correctness |
| `Network/` | Networking-layer invariants |
| `Protocol/` | Protocol-layer invariants (10 files) |
| `Quasar/` | Quasar Consensus (PQ-finality theorem) |
| `Storage/` | Storage-layer invariants |
| `StrictE2EPQ/` | Coverage + Profile theorems |
| `Trust/` | Trust-anchor invariants |
| `Vault/` | Custody-vault invariants |
| `Warp/` | Warp PQ messaging |

### `lean/Crypto/` — algorithm-level proofs

Top-level cryptographic primitives (one `.lean` per algorithm):

```
Age, BLS, Corona, DEKDerivation, FROST, HashChainIntegrity,
HQC, HSM, Hybrid, Magnetar, MLDSA, MLKEM, NonCustodial,
SLHDSA, Threshold_Lagrange, ThresholdDecrypt, VerkleTree, ZKSignature
```

Subdirectories:

| Subdir | Files |
|---|---|
| `Crypto/FHE/` | `CKKS.lean`, `TFHE.lean` |
| `Crypto/Precompile/` | 17 files — AES256GCM, BabyJubjub, BLAKE3, BLS12381, ChaCha20Poly1305, Curve25519, ECIES, Ed25519, HPKE, KZG4844, Pasta, Pedersen, Poseidon2, Secp256r1, SR25519, X25519, XWing |
| `Crypto/Pulsar/` | `OutputInterchange.lean`, `Shamir.lean`, `Unforgeability.lean`, `dkg2.lean` |
| `Crypto/Threshold/` | `CGGMP21.lean`, `Composition.lean`, `LSS.lean`, `Reshare.lean` |

## TLA+ (`tla/`) — 24 specifications

State-space model checking for DeFi + DAG + cross-chain protocols.
Includes `AMM.tla`, `CrossChainSwap.tla`, `DAGEVM.tla`, `DAGZChain.tla`,
`ExplorerReplication.tla`, `Governance.tla`, `LiquidStaking.tla`, plus
each spec's `MC_*.tla` + `.cfg` model-checking harness.

Run: `cd tla && tlc MC_<Spec>.tla -config MC_<Spec>.cfg`

## Tamarin (`tamarin/`) — 6 protocol models

Symbolic-protocol analysis (Dolev-Yao):

| File | Protocol |
|---|---|
| `tamarin/FROSTThreshold.spthy` | FROST threshold-Schnorr |
| `tamarin/MPCBridge.spthy` | MPC-based bridge handshake |
| `tamarin/pq_encryption.spthy` | PQ encryption envelope |
| `tamarin/QuasarConsensus.spthy` | Quasar consensus envelope |
| `tamarin/RNSHybridHandshake.spthy` | RNS hybrid TLS handshake |
| `tamarin/ZKVerification.spthy` | ZK proof verification protocol |

Run: `cd tamarin && tamarin-prover <File>.spthy`

## Halmos (`halmos/`) — 10 Solidity symbolic-execution suites

Bounded symbolic execution against Solidity contracts:
`AMMInvariant`, `HalmosAMM`, `HalmosBridge`, `HalmosE2E`,
`HalmosLiquidLUX`, `HalmosMarkets`, `HalmosYieldVault`,
`LiquidSolvency`, `MarketsSolvency`. Run via
`pip install halmos && halmos --contract <Name>`.

## Go property tests (`property/`) — 5 suites

| File | Property |
|---|---|
| `property/ceremony_test.go` | DKG ceremony correctness under churn |
| `property/defi_test.go` | DeFi protocol invariants |
| `property/fhe_noise_test.go` | FHE noise-growth bounds |
| `property/quasar_test.go` | Quasar consensus invariants |
| `property/replication_test.go` | Replication-layer invariants |
| `property/strict_pq_test.go` | Strict-PQ profile invariants |

Run: `cd property && GOWORK=off go test ./...`

## External proof homes

Not every proof artifact lives in this repo. Each PQ primitive keeps
its own self-contained EasyCrypt theories, Jasmin sources, and proof
artifacts in its canonical repo (post 2026-05-18 consolidation: the
pulsar-mptc submission framework was merged into luxfi/pulsar):

| Primitive | Repo | EC + Jasmin location |
|---|---|---|
| **Pulsar** (M-LWE) | `luxfi/pulsar` | `proofs/easycrypt/` + `jasmin/` + `proofs/lean-easycrypt-bridge.md` |
| **Corona** (R-LWE) | `luxfi/corona` | `proofs/easycrypt/` + `jasmin/` (in flight) |
| **Magnetar** (SLH-DSA) | `luxfi/magnetar` | `proofs/easycrypt/` + `jasmin/` (in flight) |
| **P3Q** (EVM precompile) | `luxfi/precompile/p3q` | `proofs/easycrypt/` + `jasmin/` (in flight) |
| **FROST / CGGMP21 / BLS-threshold** | `luxfi/threshold/protocols/{frost,cmp,bls}/` | `proofs/easycrypt/` + `jasmin/` (in flight) |
| **TFHE** | `luxfi/fhe` | `proofs/easycrypt/` + `jasmin/` (in flight) |
| **ML-KEM** | `luxfi/crypto/mlkem` | `proofs/easycrypt/` + `jasmin/` (in flight) |

Each per-repo `scripts/check-high-assurance.sh` orchestrates the EC +
Lean bridge + Jasmin CT gates for that primitive.

## Cross-references

- `~/work/lux/papers/INDEX.md` — full paper catalogue.
- `~/work/lux/lps/CRYPTO-CANONICAL.md` — canonical crypto wiring.
- `~/work/lux/quasar/PROFILES.md` + `quasar/PRIMITIVES.md` — Quasar
  cert profile registry and primitive pin map (the supermassive
  black hole at the center of the Lux PQ-finality universe).
- `~/work/lux/lps/HANZO-CRYPTO-SUITE.md` — full Lux crypto inventory
  across all categories.

---

**Document metadata**

- Name: `INDEX.md`
- Regenerated: 2026-05-18
- Run `ls -1` from this directory to verify file lists against this catalogue.
