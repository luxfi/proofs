# Master Chronology — Lux / Hanzo / Zoo / Pars

Authoritative cross-repo timeline for the Quasar 3.0 / 4.0 chain stack.

| Date | Event | Repo / Paper |
|---|---|---|
| 2019-12 | Lux founded | `~/work/lux/` |
| 2021-10 | Zoo whitepaper coins "NFT Liquidity Protocol" | `~/work/zoo/papers/zoo-2021-original-whitepaper/` |
| 2025-12-15 | QuasarCert spec freeze | `~/work/lux/proofs/quasar-cert-soundness.tex` |
| **2025-12-25** | **Lux Quasar 3.0 chain activation** | LP-020, LP-105 |
| **2026-02-14** | **Lux Quasar 4.0 / QuasarSTM 4.0 production activation** | LP-135 |

## Per-repo chronologies

- `~/work/lux/proofs/CHRONOLOGY.md`
- `~/work/hanzo/proofs/CHRONOLOGY.md`
- `~/work/zoo/proofs/CHRONOLOGY.md`
- `~/work/pars/proofs/CHRONOLOGY.md`

## Canonical chain topology (LP-134)

Nine chains, one role each:

| Chain | Role | Key LP |
|---|---|---|
| P-Chain | Platform / staking / validator set | LP-015 |
| C-Chain | EVM contracts | LP-009 |
| X-Chain | UTXO ledger | — |
| Q-Chain | **Pulsar 2-round PQ-threshold for consensus signing** | LP-073 |
| Z-Chain | **Groth16 over BLS12-381 — N×ML-DSA-65 → 192-byte proof** | LP-063 |
| A-Chain | TEE / audit / identity attestation | LP-065 |
| B-Chain | Native bridge / cross-ecosystem messaging | LP-016 |
| M-Chain | **MPC ceremonies — bridge custody for external wallets (CGGMP21, FROST, Pulsar-general)** | LP-019, LP-076 |
| F-Chain | **TFHE bootstrap-key generation, encrypted EVM** | LP-167 |

The legacy "T-Chain" name is retained only for `teleportvm` (LP-6332,
LP-9110) — unified bridge + relay + oracle. Its prior MPC + FHE +
Groth16 + PQ-consensus duties are split across M-/F-/Z-/Q-Chain.

## Future work

- E-Chain finalisation
- Cross-chain composition with M-Chain MPC ceremonies for external
  custody, F-Chain TFHE bootstrap-key rotation, Z-Chain Groth16
  cert aggregation

## Forbidden operational taxonomy reminder

Per `~/work/lux/lps/TAXONOMY.md` and LP-134 §Forbidden operational
names — the operational identifiers in Lux LPs, code, papers, and
config keys are exclusively:

- VMs: `PVM`, `EVM`, `XVM`, `QVM`, `ZVM`, `AIVM`, `BVM`, `MVM`, `FVM`
- Consensus family: **Quasar / Photon / Wave / Focus / Prism /
  Horizon / Flare / Ray / Field / Nova / Nebula**
- PQ threshold: **Pulsar** (Lux variant of Ringtail with DKG2 +
  Pulsar-SHA3 hash suite)

The metastable linear-chain consensus prior art (Team Rocket et al.
2018) is acknowledged in academic citations in LP-110 §References [4]
**only** as historical prior art. Live operational identifiers,
chain aliases, and code symbols MUST use the Lux taxonomy above.
