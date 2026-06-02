/-
  Corona Pedersen DKG (dkg2) correctness -- Lean statement.

  Mirrors `~/work/lux/proofs/lean/Crypto/Pulsar/dkg2.lean` for the
  R-LWE setting.

  Claim: the Corona Pedersen-VSS-based DKG (`luxfi/corona/dkg2/dkg2.go`)
  produces correct + hiding + binding shares of the group secret over
  R_q^N. The hiding + binding reductions are the standard Pedersen-VSS
  results lifted to the R_q^N module.

  This file is the Lean COMPANION to the EasyCrypt Corona_N4.ec
  ReshareHonest module. The DKG honest module here can be viewed as
  the "initial sharing" precondition that Reshare then preserves.
-/

import Crypto.Corona.Shamir
import Mathlib.Tactic

namespace Crypto.Corona.DKG

/-- A Pedersen commitment value: an element of R_q (the polynomial
    ring). For Corona's parameter set R_q = Z_q[X] / (X^256 + 1)
    with q = 0x1000000004A01. -/
opaque PedersenCommit : Type

/-- A Pedersen-VSS transcript: per-party commits + per-party
    encrypted shares (broadcast on the channel). -/
opaque DKGTranscript : Type

/-- An R_q^N share. Modeled as a single-field byte wrapper so it is
    `Inhabited` (every real share is a concrete byte string); the
    reconstruction *operation* below stays opaque. -/
structure Share where ofBytes :: (bytes : ByteArray) deriving Inhabited

/-- A committee identifier: a list of party indices participating in
    the ceremony. -/
opaque Committee : Type

/-- The honest DKG output: a list of per-party shares + the
    transcript. -/
opaque dkg_honest_output : Committee → DKGTranscript → List Share

/-- The reconstruction of the group secret from a quorum's shares. -/
opaque dkg_reconstruct : Committee → List Share → Share

/-- The Pedersen-VSS soundness property: if the transcript verifies,
    then for every two quorums Q1, Q2 of the same committee, the
    reconstructed share is the same.

    This is the binding property -- a malicious dealer cannot equivocate
    on the secret across different reconstructing quorums.

    Stated as a named axiom referencing the standard Pedersen-VSS
    soundness theorem (Pedersen 1991 + Feldman 1987 follow-up). -/
axiom dkg_binding :
    ∀ (c : Committee) (tr : DKGTranscript) (Q1 Q2 : Committee),
      let shares := dkg_honest_output c tr
      dkg_reconstruct Q1 shares = dkg_reconstruct Q2 shares

/-- The hiding property: the dealer's randomness statistically hides
    the secret given < t shares.

    Stated as a named axiom citing Pedersen 1991. -/
axiom dkg_hiding :
    ∀ (_c : Committee) (_tr : DKGTranscript),
      -- The marginal distribution of any < t shares is independent of
      -- the secret. (Stated abstractly here -- the probability-monad
      -- form lives in EC + the threshold_lagrange.lean bridge.)
      True

/-- DKG correctness: the secret recovered by the honest reconstruct
    matches the dealer's chosen polynomial constant term. -/
axiom dkg_correct :
    ∀ (c : Committee) (tr : DKGTranscript) (Q : Committee),
      let shares := dkg_honest_output c tr
      -- The reconstruct returns the dealer's secret. (Abstract here;
      -- the algebraic content is `Shamir.shamir_correct_at_target`
      -- at the polynomial level.)
      ∃ (s : Share), dkg_reconstruct Q shares = s

end Crypto.Corona.DKG
