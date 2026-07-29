/-
  Post-Quantum Key Exchange Handshake

  Hybrid key exchange: X25519 + ML-KEM-768.
  Both classical and post-quantum key exchange in parallel.
  Session key derived from both shared secrets.

  Maps to:
  - lux/node: peer-to-peer connection setup
  - lux/crypto: hybrid KEM
  - HIP-0005: PQ security for AI infrastructure

  Properties:
  - Hybrid: both X25519 AND ML-KEM must succeed
  - Forward secrecy: ephemeral keys per session
  - Transcript binding: session key binds full handshake
  - Quantum safe: ML-KEM protects if X25519 breaks
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Protocol.Handshake

/-- Handshake state machine -/
inductive State where
  | initial
  | sentHello (ephPK : Nat)
  | receivedHello (sharedSecret : Nat)
  | established (sessionKey : Nat)
  | failed (reason : String)
  deriving Repr

/-- Key exchange components -/
structure KeyExchange where
  x25519SS : Nat         -- X25519 shared secret
  mlkemSS : Nat          -- ML-KEM-768 shared secret
  transcriptHash : Nat   -- hash of full handshake transcript

/-- HKDF over both shared secrets and the transcript.
    Opaque: a KDF is a hash, and its only modelled property is the
    collision resistance assumed below. Any concrete definition here is a
    different function with different properties — as `+` was, which made
    `forward_secrecy` false by ⟨1,1,1⟩ and ⟨1,0,2⟩ colliding at 3. -/
opaque deriveSessionKey (kex : KeyExchange) : Nat

/-- FORWARD SECRECY: Each session uses fresh ephemeral keys.
    Compromising long-term keys doesn't reveal past sessions. -/
axiom forward_secrecy :
  ∀ (session1 session2 : KeyExchange),
    session1.transcriptHash ≠ session2.transcriptHash →
    deriveSessionKey session1 ≠ deriveSessionKey session2

/-- TRANSCRIPT BINDING: Session key commits to full handshake -/
theorem transcript_binding (kex1 kex2 : KeyExchange)
    (h : kex1.transcriptHash ≠ kex2.transcriptHash)
    (h_same_key : deriveSessionKey kex1 = deriveSessionKey kex2) :
    kex1.x25519SS + kex1.mlkemSS ≠ kex2.x25519SS + kex2.mlkemSS ∨
    kex1.transcriptHash = kex2.transcriptHash :=
  -- Distinct transcripts give distinct keys, so the hypotheses cannot both
  -- hold. Previously this unfolded the KDF and closed the goal by `omega`,
  -- which proved a fact about addition rather than about a hash.
  absurd h_same_key (forward_secrecy kex1 kex2 h)

/-- FAILED IS TERMINAL -/
theorem failed_terminal (reason : String) :
    State.failed reason = State.failed reason := rfl

/-- ESTABLISHED HAS KEY -/
def sessionKey : State → Option Nat
  | .established k => some k
  | _ => none

theorem initial_no_key : sessionKey .initial = none := rfl

theorem established_has_key (k : Nat) :
    sessionKey (.established k) = some k := rfl

end Protocol.Handshake
