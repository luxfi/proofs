# Pulsar proofs

LaTeX theorem statements + proofs for Pulsar (Module-LWE),
the FIPS 204-compatible sibling of Pulsar (R-LWE). Each file is
included from `~/work/lux/pulsar/spec/pulsar.tex` or from a
paper.

| file | claim |
|---|---|
| `unforgeability.tex` | TS-UF reduction to MLWE + MSIS + ML-DSA EUF-CMA |
| `scaling.tex` | Concrete claims at the extreme committee size N* = 1,111,111 |
| `output-interchangeability.tex` | Class N1 manifesto: Pulsar signatures verify under unmodified FIPS 204 |
| `dkg-soundness.tex` | DKG soundness + share privacy |
| `reshare-preservation.tex` | Reshare preserves pk, soundness, privacy under beacon-randomised quorum |
| `grouped-sortition.tex` | Pulsar (3,2) × Quasar sortition × P3Q rollup composition (the production 1.1M-validator stack); fully PQ end-to-end |

The R-LWE Pulsar proofs live in the parent `proofs/pulsar/`
directory and target the Pulsar (Class S1+S4) submission. Do not
confuse the two: Pulsar.R has its own R_q ring-degree polynomial
shape and verifier; Pulsar.M (this directory) operates over R_q^k
and verifies under the FIPS 204 verifier verbatim.

## Mechanization status

- LaTeX statements: **all five files complete**.
- Lean 4: `lean/Crypto/Pulsar/` skeleton in this repository. The reductions
  import the FIPS 204 ML-DSA EUF-CMA axiom from
  `lean/Crypto/MLDSA.lean` and the MLWE / MSIS hardness axioms from
  `lean/Crypto/Pulsar/dkg2.lean`.
- Tamarin: out of scope (Tamarin targets the auth-permit protocol,
  not the threshold cryptography).
- Halmos: out of scope (Halmos targets Solidity invariants).

## Reference implementation cross-check

| theorem | reference implementation gate |
|---|---|
| `thm:pulsar-tsuf` | `ref/go/pkg/pulsar/threshold_test.go` |
| `thm:pulsar-scales-n` | `ref/go/pkg/pulsar/shamir_gfq_test.go` (boundary committees) |
| `prop:pulsar-correct-at-N-star` | `ref/go/pkg/pulsar/largeshamir_test.go:TestLargeShamir_EvalAtTargetCommitteeSize` |
| `thm:pulsar-output-interchange` | `ref/go/pkg/pulsar/kat_test.go:TestKAT_ThresholdSign_Replay` |
| `thm:pulsar-dkg-sound` | `ref/go/pkg/pulsar/dkg_test.go` |
| `thm:pulsar-reshare-pkinv` | `ref/go/pkg/pulsar/reshare_test.go` |
