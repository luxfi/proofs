# Infrastructure Status — 2026-04-20

Snapshot of live chains, exchanges, bridges, and wallets across the
Lux / Hanzo / Zoo / Liquidity / Pars stack as of the joint Liquidity
Protocol adoption date.

## Live Chains as of 2026-04-20

| Chain | Repo | Notes |
|---|---|---|
| Lux primary network — P/C/X/Q/Z/A/B/M/F | `~/work/lux/node/` | LP-134 activation set, all live; D-Chain reserved (Liquidity stack), E-Chain reserved (post-2026-04-21) |
| Zoo L1 (with Zoo D/E/F-Chain white-label resells of Lux templates) | `~/work/zoo/node/` (`zood`) | Single Go binary, Zoo EVM (chain id 200200/200201/200202) + Zoo DEX + Zoo FHE |
| Liquidity primary network (D/E/F-Chain white-label) | `~/work/liquidity/node/` | Sovereign L1, chain id 8675309 (mainnet) / 8675310 (testnet) / 8675311 (devnet) |
| Hanzo AI Chain (= Lux A-Chain branded) | `~/work/lux/node/` (A-Chain) | AIVM running on Lux primary network, Hanzo brand on operator-facing surface |
| Pars chain | `~/work/pars/node/` (`parsd`) | Sovereign L1, chain id 494949 mainnet / 7071 testnet |

## Live Exchanges

| Exchange | Repo | Notes |
|---|---|---|
| Lux DEX (LX) | `~/work/lx/dex/` | 434M ops/sec on GPU, 1M ops/sec on CPU; multi-engine (Go/C++/Rust/MLX); JSON-RPC, gRPC, WebSocket, QZMQ, ZAP |
| Zoo DEX | `~/work/zoo/node/` (Zoo DEX VM in `zood`) | CLOB + AMM, ZOO/USDT and ZOO/ETH pairs; D-Chain reseller of Lux DEX template |
| Liquidity DEX (D-Chain white-label, ATS / BD / TA-regulated) | `~/work/liquidity/dex/` (in liquidity infra; sovereign L1 nodes in `~/work/liquidity/node/`) | 12K+ markets, ATS-N + Reg NMS Rules 610/611/612 compliant; matching engine = LX DEX |

## Live Bridges

| Bridge | Repo | Notes |
|---|---|---|
| Lux B-Chain native bridge | `~/work/lux/bridge/` | BVM, cross-ecosystem messaging |
| Zoo Bridge | `~/work/zoo/bridge/` | Single Go binary, k8s-deployed |
| Cross-chain cert-lane routing | `~/work/lux/node/` (warp module) | Quasar cert-bound message delivery, exactly-once; see `lean/Warp/Delivery.lean` |

## Live Wallets

| Wallet | Repo | Notes |
|---|---|---|
| Lux Wallet | `~/work/lux/wallet/` | HD, multi-chain, hardware-wallet integration |
| Lux dWallet (decentralised wallet) | `~/work/lux/dwallet/` | Distributed key-share model |

## Status verdict

All chains, exchanges, and bridges listed above are **LIVE** as of
2026-04-20.

The two **future-work** items (still tracked for activation post
2026-04-21):

1. **D-Chain bring-up** — LP-134 reserves D-Chain for the Liquidity
   stack execution layer on Lux primary network. Operationally
   distinct from the Liquidity-sovereign-L1 (which is already live).
2. **E-Chain bring-up** — reserved per LP-134; not yet wired.

Neither blocks the 2026-04-01 launch nor the 2026-04-20 cross-org
adoption.

## Cross-references

- `~/work/lux/lps/LP-134-lux-chain-topology.md` — chain topology
- `~/work/lux/lps/TAXONOMY.md` — naming
- `~/work/liquidity/CLAUDE.md` — Liquidity service map
- `~/work/zoo/node/CLAUDE.md` — `zood` binary
- `~/work/lx/dex/CLAUDE.md` — DEX architecture
- `~/work/pars/LLM.md` — Pars precompile registry
