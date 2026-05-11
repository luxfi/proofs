# LUX_STRICT_E2E_PQ formal proof tree

Machine-checked counterparts to the LUX_STRICT_E2E_PQ paper
(`luxfi/papers/lp-stricte2epq/`).

The strict-e2e-pq profile pins every byte that gates a state transition on
Lux to a FIPS 203 / 204 / 205 primitive or a SHA3-family transcript. This
directory carries the proofs of the underlying soundness claims, the TLA+
state machine for the profile lifecycle, and the Go property tests that
exercise the canonical Go code under both strict and permissive profiles.

See [LP-105 §Claims and evidence](https://github.com/luxfi/lps/blob/main/LP-105-lux-stack-lexicon.md#claims-and-evidence)
for the canonical claims/evidence table.

## Files

| File | Language | Purpose |
|------|----------|---------|
| `strict-e2e-pq-soundness.tex` | LaTeX | formal soundness statement (companion to lp-stricte2epq §13) |
| `../tla/StrictPQProfile.tla` | TLA+ | profile state machine and SchemeGate invariant |
| `../tla/MC_StrictPQProfile.tla` | TLA+ | TLC model checker config |
| `../lean/StrictE2EPQ/Profile.lean` | Lean 4 | `IsE2EPQ profile` proposition |
| `../lean/StrictE2EPQ/Coverage.lean` | Lean 4 | 14-path PQ coverage theorem |
| `../property/strict_pq_test.go` | Go | property tests against `luxfi/consensus` |

## Build

```bash
# Lean 4
cd ../lean && lake build StrictE2EPQ

# TLA+
cd ../tla && tlc MC_StrictPQProfile.tla

# Go property tests
cd ../property && GOWORK=off go test ./...
```

## Soundness statement

Under `LUX_STRICT_E2E_PQ`:

1. Every signed transaction is verified under ML-DSA-65 (FIPS 204).
2. `tx_auth_root` inclusion is sound under SHA3-384 Merkle.
3. `ComputeRoundDigest` is collision-resistant under SHA3-384.
4. Pulsar-M finality signatures verify under M-LWE soundness.
5. Profile-bumps are the only mechanism that can relax the posture; the
   pinned digest is the operator-visible barrier.

See `strict-e2e-pq-soundness.tex` for the formal statement; see
`Profile.lean` and `Coverage.lean` for the Lean 4 propositions.
