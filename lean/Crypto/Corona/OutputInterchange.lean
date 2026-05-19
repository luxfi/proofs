/-
  Corona Output-Interchangeability (Class N1) -- Lean formalization.

  Mirrors `~/work/lux/proofs/lean/Crypto/Pulsar/OutputInterchange.lean`
  for the R-LWE setting.

  Claim: every signature byte string produced by Corona's threshold
  Combine procedure on inputs `(group_pk = (A, bTilde), m, ctx, quorum,
  shares)` (satisfying the protocol invariants) verifies under the
  Corona reference verifier `Verify(group_pk, m, σ)`.

  EasyCrypt counterpart:
    `~/work/lux/corona/proofs/easycrypt/Corona_N1_Extracted.ec`
    `corona_n1_byte_equality_extracted` (equiv form).
-/

import Crypto.Corona.Shamir
import Crypto.Threshold_Lagrange
import Mathlib.Tactic

namespace Crypto.Corona.OutputInterchange

/-- Abstract types for the protocol layer. -/
opaque GroupPk : Type
opaque Share : Type
opaque Signature : Type
opaque Message : Type
opaque Ctx : Type
opaque Randomness : Type
opaque Quorum : Type

/-- The Corona Verify predicate. -/
opaque verify : GroupPk → Message → Ctx → Signature → Bool

/-- The Corona threshold Combine output: byte string of the final
    signature. -/
opaque threshold_combine :
  GroupPk → Message → Ctx → Quorum → List Share → Randomness → Signature

/-- The centralized Boschini Sign output on the reconstructed share. -/
opaque central_sign :
  Share → Message → Ctx → Randomness → Signature

/-- Lagrange reconstruction of the shares. -/
opaque reconstruct : Quorum → List Share → Share

/-- The public-key derivation map: secret -> public. -/
opaque derive_pk : Share → GroupPk

/-- The honest-quorum / accept-path predicate. -/
opaque accept_path : Share → Message → Ctx → Randomness → Prop

/-- Class N1 byte-equality: threshold Combine = central Sign on the
    reconstructed share, byte-for-byte. This is the Lean statement of
    the EC `corona_n1_byte_equality_extracted` theorem.

    Stated as a named axiom because it is bridged to the EC proof; the
    Lean side does NOT re-prove the byte-walk content (that's the
    Jasmin extraction + RLWE_Functional structural identity). -/
axiom corona_n1_byte_equality
    (gpk : GroupPk) (m : Message) (ctx : Ctx) (q : Quorum)
    (shares : List Share) (rho : Randomness)
    (sk_group : Share)
    (h_recon : reconstruct q shares = sk_group)
    (h_gpk : gpk = derive_pk sk_group)
    (h_accept : accept_path sk_group m ctx rho) :
    threshold_combine gpk m ctx q shares rho
      = central_sign sk_group m ctx rho

/-- Verifier correctness on outputs of the centralized Sign.
    This is Boschini ePrint 2024/1113 §3 Theorem 1, restated in Lean
    as a named axiom (the proof is in the cited paper). -/
axiom corona_central_verify_correct
    (sk : Share) (m : Message) (ctx : Ctx) (rho : Randomness)
    (h_accept : accept_path sk m ctx rho) :
    verify (derive_pk sk) m ctx (central_sign sk m ctx rho) = true

/-- Class N1 output interchangeability (the verifier-compatibility
    corollary): every honest-quorum Corona signature verifies under
    the same group public key.

    Discharged: chains the byte-equality (`corona_n1_byte_equality`)
    with the verifier correctness (`corona_central_verify_correct`). -/
theorem corona_output_interchangeable
    (gpk : GroupPk) (m : Message) (ctx : Ctx) (q : Quorum)
    (shares : List Share) (rho : Randomness)
    (sk_group : Share)
    (h_recon : reconstruct q shares = sk_group)
    (h_gpk : gpk = derive_pk sk_group)
    (h_accept : accept_path sk_group m ctx rho) :
    verify gpk m ctx (threshold_combine gpk m ctx q shares rho) = true := by
  rw [corona_n1_byte_equality gpk m ctx q shares rho sk_group
        h_recon h_gpk h_accept]
  rw [h_gpk]
  exact corona_central_verify_correct sk_group m ctx rho h_accept

/-- Convenience theorem: byte-equality up to the group-pk-derivation
    consistency. This is the cleanest statement reviewers should cite
    when reading the EC bridge. -/
theorem corona_verify_is_construction_dispatch
    (gpk : GroupPk) (m : Message) (ctx : Ctx) (q : Quorum)
    (shares : List Share) (rho : Randomness)
    (sk_group : Share)
    (h_recon : reconstruct q shares = sk_group)
    (h_gpk : gpk = derive_pk sk_group)
    (h_accept : accept_path sk_group m ctx rho) :
    threshold_combine gpk m ctx q shares rho
      = central_sign sk_group m ctx rho :=
  corona_n1_byte_equality gpk m ctx q shares rho sk_group
    h_recon h_gpk h_accept

end Crypto.Corona.OutputInterchange
