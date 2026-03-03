# Lux Proofs

> Lux is not merely adding post-quantum signatures to a chain; it defines a hybrid finality architecture for DAG-native consensus, with protocol-agnostic threshold lifecycle, post-quantum threshold sealing, and cross-chain propagation of Horizon finality.

See [LP-105 §Claims and evidence](https://github.com/luxfi/lps/blob/main/LP-105-lux-stack-lexicon.md#claims-and-evidence) for the canonical claims/evidence table and the ten architectural commitments — single source of truth.

Machine-checked proofs, protocol specifications, and property tests for the Lux consensus stack.

## Inventory

| Tool | Files | Path |
|------|------:|------|
| Lean 4 | 72 | `lean/` |
| TLA+ | 22 | `tla/` |
| Halmos | 10 | `halmos/` |
| Tamarin | 6 | `tamarin/` |
| Go property tests | 4 | `property/` |
| **Total** | **114** | |

## Build and Run

```bash
# Lean 4
cd lean && lake build

# TLA+
cd tla && tlc MC_Wave.tla

# Halmos
pip install halmos
cd halmos && halmos --contract LiquidSolvencyTest

# Tamarin
cd tamarin && tamarin-prover QuasarConsensus.spthy

# Go property tests
cd property && GOWORK=off go test ./...
```

## Lean 4 Proofs (72 files)

### Consensus (11)

| File | Property |
|------|----------|
| `Consensus/Safety.lean` | No two honest nodes finalize conflicting values |
| `Consensus/Liveness.lean` | Progress under partial synchrony |
| `Consensus/BFT.lean` | Quorum intersection (2f+1 of 3f+1) |
| `Consensus/Finality.lean` | Finalized values are permanent |
| `Consensus/Quasar.lean` | BLS+Ringtail+ML-DSA triple hybrid composition |
| `Consensus/ThresholdProof.lean` | Threshold signature scheme correctness |
| `Consensus/PreferenceStability.lean` | Preference stability under adversary |
| `Consensus/Validator.lean` | Validator set properties |
| `Consensus/DAGEVM.lean` | Block-STM-as-consensus: serialisability, commutativity, no-double-spend |
| `Consensus/DAGZChain.lean` | Nullifier-disjoint antichains; parallel-verify soundness; FHE linearity |
| `Consensus/PQZParallel.lean` | Cross-chain non-interference; Quasar stamps independent; linear-scaling validator signing |

### Protocol (10)

| File | Property |
|------|----------|
| `Protocol/Wave.lean` | Threshold voting convergence |
| `Protocol/Flare.lean` | DAG cert/skip 2f+1 correctness |
| `Protocol/Ray.lean` | Linear chain finality |
| `Protocol/Field.lean` | DAG committed prefix consistency |
| `Protocol/Quasar.lean` | BLS+Ringtail hybrid aggregation |
| `Protocol/Photon.lean` | Committee selection uniformity |
| `Protocol/Prism.lean` | Fisher-Yates unbiased k-subsets |
| `Protocol/Handshake.lean` | Protocol handshake correctness |
| `Protocol/Nebula.lean` | Nebula protocol properties |
| `Protocol/Nova.lean` | Nova protocol properties |

### Crypto (20)

| File | Property |
|------|----------|
| `Crypto/BLS.lean` | Aggregation correctness + rogue key resistance |
| `Crypto/FROST.lean` | t-of-n threshold unforgeability |
| `Crypto/Ringtail.lean` | LWE-based threshold unforgeability (PQ) |
| `Crypto/MLDSA.lean` | FIPS 204 signature correctness |
| `Crypto/MLKEM.lean` | FIPS 203 key encapsulation |
| `Crypto/SLHDSA.lean` | SLH-DSA signature correctness |
| `Crypto/Hybrid.lean` | Triple hybrid identity sig (Ed25519+ML-DSA+SLH-DSA) |
| `Crypto/Age.lean` | Age encryption properties |
| `Crypto/DEKDerivation.lean` | Data encryption key derivation |
| `Crypto/HashChainIntegrity.lean` | Hash chain integrity |
| `Crypto/HSM.lean` | HSM security model |
| `Crypto/NonCustodial.lean` | Non-custodial key properties |
| `Crypto/ThresholdDecrypt.lean` | Threshold decryption |
| `Crypto/VerkleTree.lean` | Verkle tree correctness |
| `Crypto/FHE/CKKS.lean` | CKKS homomorphic encryption |
| `Crypto/FHE/TFHE.lean` | TFHE homomorphic encryption |
| `Crypto/Threshold/CGGMP21.lean` | CGGMP21 threshold ECDSA |
| `Crypto/Threshold/Composition.lean` | Threshold composition |
| `Crypto/Threshold/LSS.lean` | Linear secret sharing |
| `Crypto/Threshold/Reshare.lean` | Share resharing |

### DeFi (8)

| File | Property |
|------|----------|
| `DeFi/AMM.lean` | AMM invariants |
| `DeFi/FeeModel.lean` | Fee model correctness |
| `DeFi/FlashLoan.lean` | Flash loan safety |
| `DeFi/Governance.lean` | Governance properties |
| `DeFi/HFT.lean` | HFT fairness |
| `DeFi/LiquidStaking.lean` | Liquid staking safety |
| `DeFi/OrderBook.lean` | Order book invariants |
| `DeFi/Router.lean` | Swap router correctness |

### Bridge / Warp (8)

| File | Property |
|------|----------|
| `Bridge/FillIntegrity.lean` | Bridge fill integrity |
| `Bridge/OmnichainRouter.lean` | Omnichain routing correctness |
| `Bridge/ShariaFilter.lean` | Compliance filter properties |
| `Bridge/Teleport.lean` | Teleport bridge correctness |
| `Bridge/YieldVault.lean` | Yield vault safety |
| `Warp/Delivery.lean` | Exactly-once message delivery |
| `Warp/Ordering.lean` | Causal ordering preservation |
| `Warp/Security.lean` | Warp message security |

### GPU (4)

| File | Property |
|------|----------|
| `GPU/ConsensusScaling.lean` | GPU consensus scaling |
| `GPU/DEXScaling.lean` | GPU DEX scaling |
| `GPU/EVMScaling.lean` | GPU EVM scaling |
| `GPU/FHEScaling.lean` | GPU FHE scaling |

### Build (4)

| File | Property |
|------|----------|
| `Build/Attestation.lean` | Build attestation |
| `Build/Coeffect.lean` | Coeffect tracking |
| `Build/Ecosystem.lean` | Ecosystem properties |
| `Build/Reproducibility.lean` | Reproducible builds |

### Storage (2)

| File | Property |
|------|----------|
| `Storage/Replicate.lean` | Replication correctness |
| `Storage/ZapDB.lean` | ZapDB properties |

### Trust (3)

| File | Property |
|------|----------|
| `Trust/Authority.lean` | Authority properties |
| `Trust/Revocation.lean` | Revocation correctness |
| `Trust/Vouch.lean` | Vouch chain properties |

### Other (5)

| File | Property |
|------|----------|
| `Compliance/ERC3643.lean` | ERC-3643 compliance |
| `Compute/CrossChain.lean` | Cross-chain compute |
| `Network/PeerDiscovery.lean` | Peer discovery correctness |
| `Vault/KeyIsolation.lean` | Key isolation |
| `Main.lean` | Entry point |

## TLA+ Specifications (22 files)

12 specs + 10 model checker configs (`MC_*.tla`):

| Spec | MC Config | Domain |
|------|-----------|--------|
| `Wave.tla` | `MC_Wave.tla` | Wave consensus |
| `Quasar.tla` | `MC_Quasar.tla` | Quasar hybrid consensus |
| `Teleport.tla` | `MC_Teleport.tla` | Cross-chain teleport |
| `AMM.tla` | `MC_AMM.tla` | AMM invariants |
| `Orderbook.tla` | `MC_Orderbook.tla` | Order book matching |
| `Oracle.tla` | `MC_Oracle.tla` | Oracle price feed |
| `Governance.tla` | `MC_Governance.tla` | Governance voting |
| `LiquidStaking.tla` | `MC_LiquidStaking.tla` | Liquid staking |
| `VaultSync.tla` | `MC_VaultSync.tla` | Vault synchronization |
| `CrossChainSwap.tla` | `MC_CrossChainSwap.tla` | Cross-chain swap atomicity |
| `ExplorerReplication.tla` | `MC_ExplorerReplication.tla` | Explorer data replication |

## Halmos Symbolic Execution (10 files)

| File | Target |
|------|--------|
| `AMMInvariant.t.sol` | AMM constant product |
| `HalmosAMM.t.sol` | AMM operations |
| `HalmosBridge.t.sol` | Bridge solvency |
| `HalmosE2E.t.sol` | End-to-end flows |
| `HalmosLiquidLUX.t.sol` | Liquid LUX staking |
| `HalmosMarkets.t.sol` | Markets invariants |
| `HalmosYieldVault.t.sol` | Yield vault safety |
| `LiquidSolvency.t.sol` | Liquid solvency |
| `MarketsSolvency.t.sol` | Markets solvency |
| `test/FHEInvariant.t.sol` | FHE invariants |

## Tamarin Protocol Verification (6 files)

| File | Protocol |
|------|----------|
| `FROSTThreshold.spthy` | FROST threshold signing |
| `MPCBridge.spthy` | MPC bridge security |
| `pq_encryption.spthy` | Post-quantum encryption |
| `QuasarConsensus.spthy` | Quasar consensus |
| `RNSHybridHandshake.spthy` | RNS hybrid handshake |
| `ZKVerification.spthy` | Zero-knowledge verification |

## Go Property Tests (4 files)

| File | Target |
|------|--------|
| `defi_test.go` | DeFi invariants |
| `fhe_noise_test.go` | FHE noise budget |
| `quasar_test.go` | Quasar consensus |
| `replication_test.go` | Replication correctness |

## Methodology

1. Model Go protocol as Lean state machine (states, transitions, invariants)
2. Prove invariants hold across all transitions (induction on steps)
3. Adversarial scheduler with f < n/3 Byzantine nodes (no network model)
4. Crypto proofs assume standard hardness (DLP, LWE) -- protocol correctness only
5. Halmos tests target economic invariants (solvency, conservation), not functional correctness
6. TLA+ specs verify liveness and fairness under model checking
7. Tamarin verifies protocol-level security properties (authentication, secrecy)
