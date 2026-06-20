# Pulsar proofs

LaTeX theorem statements + proofs for Pulsar (Module-LWE), the
FIPS 204-byte-equal threshold scheme. Its sibling is Corona, a
separate Module-LWE threshold scheme (the Ringtail-derived parameter
regime; not FIPS-byte-equal). Each file is included from
`~/work/lux/pulsar/spec/pulsar.tex` or from a paper.

| file | claim |
|---|---|
| `unforgeability.tex` | TS-UF reduction to MLWE + MSIS + ML-DSA EUF-CMA |
| `scaling.tex` | Concrete claims at the extreme committee size N* = 1,111,111 |
| `output-interchangeability.tex` | Class N1 manifesto: Pulsar signatures verify under unmodified FIPS 204 |
| `dkg-soundness.tex` | DKG soundness + share privacy |
| `reshare-preservation.tex` | Reshare preserves pk, soundness, privacy under beacon-randomised quorum |
| `grouped-sortition.tex` | Pulsar (3,2) × Quasar sortition × P3Q rollup composition (the production 1.1M-validator stack); fully PQ end-to-end |

The Corona proofs (Module-LWE, Ringtail-derived parameter regime,
module dims M=8/N=7 over R_q = Z_q[X]/(X^256+1), q 48-bit) live with
the `lean/Crypto/Corona/` tree and `luxfi/corona`. Do not confuse the
two: Corona has its own large parameter set and verifier and is not
FIPS-byte-equal; Pulsar (this directory) operates over R_q^k at the
FIPS 204 ML-DSA-65 parameters and verifies under the FIPS 204 verifier
verbatim. Both are Module-LWE — they differ in parameter regime and
lifecycle, not lattice family.

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
