# Pulsar-M proofs

LaTeX theorem statements + proofs for Pulsar-M (Module-LWE),
the FIPS 204-compatible sibling of Pulsar (R-LWE). Each file is
included from `~/work/lux/pulsar-m/spec/pulsar-m.tex` or from a
paper.

| file | claim |
|---|---|
| `unforgeability.tex` | TS-UF reduction to MLWE + MSIS + ML-DSA EUF-CMA |
| `scaling.tex` | Concrete claims at the extreme committee size N* = 1,111,111 |
| `output-interchangeability.tex` | Class N1 manifesto: Pulsar-M signatures verify under unmodified FIPS 204 |
| `dkg-soundness.tex` | DKG soundness + share privacy |
| `reshare-preservation.tex` | Reshare preserves pk, soundness, privacy under beacon-randomised quorum |
| `grouped-sortition.tex` | Pulsar-M (3,2) × Quasar sortition × P3Q rollup composition (the production 1.1M-validator stack); fully PQ end-to-end |

The R-LWE Pulsar proofs live in the parent `proofs/pulsar/`
directory and target the Pulsar (Class S1+S4) submission. Do not
confuse the two: Pulsar.R has its own R_q ring-degree polynomial
shape and verifier; Pulsar.M (this directory) operates over R_q^k
and verifies under the FIPS 204 verifier verbatim.

## Mechanization status

- LaTeX statements: **all five files complete**.
- Lean 4: `lean/Crypto/Pulsar_M/` skeleton in flight. The reductions
  import the FIPS 204 ML-DSA EUF-CMA axiom from
  `lean/Crypto/MLDSA.lean` and the MLWE / MSIS hardness axioms from
  `lean/Crypto/Pulsar/dkg2.lean`.
- Tamarin: out of scope (Tamarin targets the auth-permit protocol,
  not the threshold cryptography).
- Halmos: out of scope (Halmos targets Solidity invariants).

## Reference implementation cross-check

| theorem | reference implementation gate |
|---|---|
| `thm:pulsar-m-tsuf` | `ref/go/pkg/pulsarm/threshold_test.go` |
| `thm:pulsar-m-scales-n` | `ref/go/pkg/pulsarm/shamir_gfq_test.go` (boundary committees) |
| `prop:pulsar-m-correct-at-N-star` | `ref/go/pkg/pulsarm/largeshamir_test.go:TestLargeShamir_EvalAtTargetCommitteeSize` |
| `thm:pulsar-m-output-interchange` | `ref/go/pkg/pulsarm/kat_test.go:TestKAT_ThresholdSign_Replay` |
| `thm:pulsar-m-dkg-sound` | `ref/go/pkg/pulsarm/dkg_test.go` |
| `thm:pulsar-m-reshare-pkinv` | `ref/go/pkg/pulsarm/reshare_test.go` |
