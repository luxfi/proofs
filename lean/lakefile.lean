import Lake
open Lake DSL

package luxFormal where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Consensus where
  srcDir := "."
  roots := #[
    `Consensus.Safety,
    `Consensus.Liveness,
    `Consensus.BFT,
    `Consensus.Quasar,
    `Consensus.Finality,
    `Consensus.Validator,
    `Consensus.ThresholdProof,
    `Consensus.PreferenceStability,
    `Consensus.DAGEVM,
    `Consensus.DAGZChain,
    `Consensus.PQZParallel
  ]

lean_lib Protocol where
  srcDir := "."
  roots := #[
    `Protocol.Wave,
    `Protocol.Flare,
    `Protocol.Ray,
    `Protocol.Field,
    `Protocol.Quasar,
    `Protocol.Nova,
    `Protocol.Nebula,
    `Protocol.Photon,
    `Protocol.Prism,
    `Protocol.Handshake
  ]

lean_lib Crypto where
  srcDir := "."
  roots := #[
    `Crypto.Age,
    `Crypto.BLS,
    `Crypto.DEKDerivation,
    `Crypto.FROST,
    `Crypto.Ringtail,
    `Crypto.MLDSA,
    `Crypto.Hybrid,
    `Crypto.SLHDSA,
    `Crypto.MLKEM,
    `Crypto.FHE.TFHE,
    `Crypto.FHE.CKKS,
    `Crypto.Threshold.CGGMP21,
    `Crypto.Threshold.LSS,
    `Crypto.Threshold.Composition,
    `Crypto.VerkleTree,
    `Crypto.ThresholdDecrypt,
    `Crypto.NonCustodial,
    `Crypto.HashChainIntegrity,
    `Crypto.HSM,
    `Crypto.Precompile.BLS12381,
    `Crypto.Precompile.BabyJubjub,
    `Crypto.Precompile.Curve25519,
    `Crypto.Precompile.Pasta,
    `Crypto.Precompile.X25519,
    `Crypto.Precompile.XWing,
    `Crypto.Precompile.AES256GCM,
    `Crypto.Precompile.ChaCha20Poly1305,
    `Crypto.Precompile.KZG4844,
    `Crypto.Precompile.Pedersen,
    `Crypto.Precompile.Poseidon2,
    `Crypto.Precompile.ECIES,
    `Crypto.Precompile.HPKE,
    `Crypto.Precompile.Secp256r1,
    `Crypto.Precompile.Ed25519,
    `Crypto.Precompile.SR25519,
    `Crypto.Precompile.BLAKE3,
    `Crypto.Threshold.Reshare,
    `Crypto.ZKSignature
  ]

lean_lib Storage where
  srcDir := "."
  roots := #[
    `Storage.Replicate,
    `Storage.ZapDB
  ]

lean_lib Warp where
  srcDir := "."
  roots := #[
    `Warp.Delivery,
    `Warp.Ordering,
    `Warp.Security
  ]

lean_lib Trust where
  srcDir := "."
  roots := #[
    `Trust.Authority,
    `Trust.Vouch,
    `Trust.Revocation
  ]

lean_lib Build where
  srcDir := "."
  roots := #[
    `Build.Coeffect,
    `Build.Attestation,
    `Build.Ecosystem,
    `Build.Reproducibility
  ]

lean_lib Compute where
  srcDir := "."
  roots := #[
    `Compute.CrossChain
  ]

lean_lib DeFi where
  srcDir := "."
  roots := #[
    `DeFi.OrderBook,
    `DeFi.AMM,
    `DeFi.HFT,
    `DeFi.FeeModel,
    `DeFi.LiquidStaking,
    `DeFi.Router,
    `DeFi.FlashLoan,
    `DeFi.Governance
  ]

lean_lib Network where
  srcDir := "."
  roots := #[
    `Network.PeerDiscovery
  ]

lean_lib Compliance where
  srcDir := "."
  roots := #[
    `Compliance.ERC3643
  ]

lean_lib Bridge where
  srcDir := "."
  roots := #[
    `Bridge.Teleport,
    `Bridge.FillIntegrity,
    `Bridge.OmnichainRouter,
    `Bridge.ShariaFilter,
    `Bridge.YieldVault
  ]

lean_lib GPU where
  srcDir := "."
  roots := #[
    `GPU.EVMScaling,
    `GPU.FHEScaling,
    `GPU.ConsensusScaling,
    `GPU.DEXScaling
  ]

lean_lib Vault where
  srcDir := "."
  roots := #[
    `Vault.KeyIsolation
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
