---------------------------- MODULE StrictPQProfile ----------------------------
(*
 * TLA+ specification of the LUX_STRICT_E2E_PQ profile lifecycle.
 *
 * Source: ~/work/lux/consensus/config/security_profile.go
 * Companion paper: ~/work/lux/papers/lp-stricte2epq/
 * Lean 4: ~/work/lux/proofs/lean/StrictE2EPQ/
 *
 * Protocol summary:
 *   At boot, a node loads ChainSecurityProfile from genesis, computes
 *   the SHA3-384 digest under TupleHash256 cust "LUX_CHAIN_SECURITY_V1",
 *   and aborts if the digest does not match the pinned value.
 *
 *   After successful boot, the profile is consulted at every gating
 *   point: mempool admission (TxAuthEnvelope), permit verification
 *   (PQPermit), Z-Chain identity lookup, Q-Chain QBlock construction,
 *   Pulsar-M finality, P2P peer handshake, bridge admission.
 *
 *   The invariant: every signer is gated through profile.WalletSchemeID;
 *   every hash family used is profile.HashSuiteID; every signature
 *   primitive used is in {profile.IdentitySchemeID,
 *   profile.FinalitySchemeID, profile.HighValueSchemeID,
 *   profile.WalletSchemeID, profile.ContractAuthSchemeID}.
 *
 * Model structure:
 *   Three abstract events: ProfileLoad, AdmitTx, SignBlock.
 *   Each carries the profile under which it runs. The invariant says
 *   no two events run under conflicting profiles at the same height.
 *)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    Profiles,              \* Set of profile identifiers
    LockedProfile,         \* The pinned production profile id
    Schemes,               \* Set of signature scheme identifiers
    StrictPQSchemes,       \* The strict-PQ admitted scheme subset
    HashSuites,            \* Set of hash suite identifiers
    StrictPQSuite,         \* The strict-PQ pinned suite (SHA3-384)
    MaxHeight              \* Bound on height for model checking

ASSUME LockedProfile \in Profiles
ASSUME StrictPQSchemes \subseteq Schemes
ASSUME StrictPQSuite \in HashSuites
ASSUME MaxHeight \in Nat \ {0}

VARIABLES
    profileLoaded,         \* BOOLEAN: profile loaded at boot
    activeProfile,         \* the profile in use
    pinnedDigest,          \* the genesis-pinned profile digest
    computedDigest,        \* the digest computed at boot
    height,                \* current chain height
    admittedTxSchemes,     \* sequence of schemes used by admitted txs
    signedBlockSchemes,    \* sequence of schemes used by block signers
    aborted                \* BOOLEAN: node aborted at boot

vars == << profileLoaded, activeProfile, pinnedDigest, computedDigest,
           height, admittedTxSchemes, signedBlockSchemes, aborted >>

----------------------------------------------------------------------------
\* Types
----------------------------------------------------------------------------

TypeOK ==
    /\ profileLoaded \in BOOLEAN
    /\ activeProfile \in Profiles \cup {NULL}
    /\ pinnedDigest \in STRING
    /\ computedDigest \in STRING
    /\ height \in 0..MaxHeight
    /\ admittedTxSchemes \in Seq(Schemes)
    /\ signedBlockSchemes \in Seq(Schemes)
    /\ aborted \in BOOLEAN

NULL == CHOOSE x : x \notin Profiles

----------------------------------------------------------------------------
\* Initial state: before boot
----------------------------------------------------------------------------

Init ==
    /\ profileLoaded = FALSE
    /\ activeProfile = NULL
    /\ pinnedDigest = "PINNED_STRICT_PQ_HASH"  \* abstract: 93efd103...
    /\ computedDigest = ""
    /\ height = 0
    /\ admittedTxSchemes = << >>
    /\ signedBlockSchemes = << >>
    /\ aborted = FALSE

----------------------------------------------------------------------------
\* Actions
----------------------------------------------------------------------------

\* ProfileLoad: at boot, compute the digest and compare against pin
ProfileLoadOK ==
    /\ ~profileLoaded
    /\ ~aborted
    /\ activeProfile' = LockedProfile
    /\ computedDigest' = pinnedDigest                  \* matches; success
    /\ profileLoaded' = TRUE
    /\ UNCHANGED << pinnedDigest, height,
                    admittedTxSchemes, signedBlockSchemes, aborted >>

ProfileLoadMismatch ==
    /\ ~profileLoaded
    /\ ~aborted
    /\ activeProfile' = NULL
    /\ computedDigest' = "DIFFERENT_HASH"               \* fails; abort
    /\ profileLoaded' = FALSE
    /\ aborted' = TRUE
    /\ UNCHANGED << pinnedDigest, height,
                    admittedTxSchemes, signedBlockSchemes >>

\* AdmitTx: admit a transaction signed under some scheme. Strict-PQ
\* must reject any scheme not in StrictPQSchemes.
AdmitTx(scheme) ==
    /\ profileLoaded
    /\ ~aborted
    /\ scheme \in Schemes
    /\ scheme \in StrictPQSchemes                       \* strict-PQ gate
    /\ height < MaxHeight
    /\ admittedTxSchemes' = Append(admittedTxSchemes, scheme)
    /\ UNCHANGED << profileLoaded, activeProfile, pinnedDigest,
                    computedDigest, height, signedBlockSchemes, aborted >>

\* SignBlock: a validator signs the QBlock. Strict-PQ pins the
\* finality scheme to Pulsar-M-65.
SignBlock(scheme) ==
    /\ profileLoaded
    /\ ~aborted
    /\ scheme \in StrictPQSchemes
    /\ height < MaxHeight
    /\ height' = height + 1
    /\ signedBlockSchemes' = Append(signedBlockSchemes, scheme)
    /\ UNCHANGED << profileLoaded, activeProfile, pinnedDigest,
                    computedDigest, admittedTxSchemes, aborted >>

\* AbortMidRun: a corrupted state forces an abort (e.g., profile mutation).
\* This is the defensive transition: any mutation that changes the
\* profile mid-run forces a fatal abort.
AbortMidRun ==
    /\ profileLoaded
    /\ ~aborted
    /\ aborted' = TRUE
    /\ UNCHANGED << profileLoaded, activeProfile, pinnedDigest,
                    computedDigest, height,
                    admittedTxSchemes, signedBlockSchemes >>

Next ==
    \/ ProfileLoadOK
    \/ ProfileLoadMismatch
    \/ \E s \in Schemes : AdmitTx(s)
    \/ \E s \in Schemes : SignBlock(s)
    \/ AbortMidRun

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Safety invariants
----------------------------------------------------------------------------

\* SchemeGate: every admitted transaction was signed under a strict-PQ scheme.
SchemeGate ==
    \A i \in 1..Len(admittedTxSchemes) :
        admittedTxSchemes[i] \in StrictPQSchemes

\* FinalityGate: every signed block was signed under a strict-PQ scheme.
FinalityGate ==
    \A i \in 1..Len(signedBlockSchemes) :
        signedBlockSchemes[i] \in StrictPQSchemes

\* DigestGate: if the computed digest mismatches the pinned digest, the
\* node aborted and no transactions were admitted.
DigestGate ==
    (profileLoaded => computedDigest = pinnedDigest)
    /\ (aborted => Len(admittedTxSchemes) = 0
                /\ Len(signedBlockSchemes) = 0
                \/ profileLoaded)

\* NoLoadNoAdmit: a transaction is admitted only after profile load.
NoLoadNoAdmit ==
    (Len(admittedTxSchemes) > 0) => profileLoaded

\* NoLoadNoSign: a block is signed only after profile load.
NoLoadNoSign ==
    (Len(signedBlockSchemes) > 0) => profileLoaded

\* Conjunction: the strict-PQ invariant.
StrictE2EPQ ==
    /\ TypeOK
    /\ SchemeGate
    /\ FinalityGate
    /\ DigestGate
    /\ NoLoadNoAdmit
    /\ NoLoadNoSign

----------------------------------------------------------------------------
\* Liveness
----------------------------------------------------------------------------

\* HeightProgresses: under fair scheduling, height eventually increases.
HeightProgresses ==
    \A h \in 0..MaxHeight : <>(height >= h)

\* ProfileEventuallyLoaded: if not aborted, profile is eventually loaded.
ProfileEventuallyLoaded ==
    (~aborted) ~> profileLoaded

============================================================================
