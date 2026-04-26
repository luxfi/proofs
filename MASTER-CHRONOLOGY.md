# Master Chronology — Lux / Hanzo / Zoo / Pars / Liquidity

Authoritative cross-repo timeline for the Quasar 3.0 / 4.0 chain stack
and the Liquidity Protocol launch and adoption events.

| Date | Event | Repo / Paper |
|---|---|---|
| 2019-12 | Lux founded | `~/work/lux/` |
| 2021-10 | Zoo whitepaper coins "NFT Liquidity Protocol" | `~/work/zoo/papers/zoo-2021-original-whitepaper/` |
| 2025-12-15 | QuasarCert spec freeze | `~/work/lux/proofs/quasar-cert-soundness.tex` |
| **2025-12-25** | **Lux Quasar 3.0 chain activation** | LP-020, LP-105 |
| **2026-02-14** | **Lux Quasar 4.0 / QuasarSTM 4.0 production activation** | LP-135 |
| **2026-04-01** | **Liquidity Protocol formal launch** by Liquidity.io | `~/work/liquidity/proofs/LAUNCH-2026-04-01.md` |
| **2026-04-20** | **Lux, Hanzo, Zoo, Pars formally adopt Liquidity Protocol** | (see below) |

## Adoption documents (all dated 2026-04-20)

| Repo | File |
|---|---|
| Lux | `~/work/lux/proofs/lux-adopts-liquidity-protocol.tex` |
| Hanzo | `~/work/hanzo/proofs/hanzo-adopts-liquidity-protocol.tex` |
| Zoo | `~/work/zoo/proofs/zoo-adopts-liquidity-protocol.tex` |
| Pars | `~/work/pars/proofs/pars-adopts-liquidity-protocol.tex` |

## Per-repo chronologies

- `~/work/lux/proofs/CHRONOLOGY.md`
- `~/work/hanzo/proofs/CHRONOLOGY.md`
- `~/work/zoo/proofs/CHRONOLOGY.md`
- `~/work/pars/proofs/CHRONOLOGY.md`

## Future work (post 2026-04-20)

- D-Chain bring-up per LP-134 (Liquidity stack execution chain on Lux)
- E-Chain finalisation
- GPU-residency invariants for OMA contracts (LP-137)
- Cross-chain composition with M-Chain MPC ceremonies
- Closing the 5 open Lean `sorry` cases in
  `~/work/liquidity/proofs/lean/` (TA conservation, ATS net antisymmetry)

## Forbidden taxonomy reminder

Per `~/work/lux/lps/TAXONOMY.md` — never use `Snowball`, `Snowflake`,
`Snowman`, `avalanche`, `avalanchego`, `ava-labs`, `avax`, `AVM`. Lux
chains are `XVM` (X-Chain), `AIVM` (A-Chain), and the consensus
family is Quasar / Photon / Wave / Focus / Nova / Nebula / Prism /
Horizon / Flare / Ray / Field.
