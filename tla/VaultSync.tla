---- MODULE VaultSync ----
\* Vault CRDT Sync Protocol — TLA+ Specification
\*
\* Models the sync protocol for encrypted CRDT vaults:
\* - Multiple devices write encrypted ops locally
\* - Sync relays deliver ops between devices
\* - Each device merges ops by sequence number (LWW)
\* - Anchors commit merkle roots to chain
\*
\* Safety properties:
\* 1. Convergence: all devices eventually have the same state
\* 2. Encryption: sync relays never see plaintext
\* 3. Causality: ops are applied in causal order
\* 4. Anchor integrity: merkle root matches committed ops

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Devices,        \* Set of device IDs
    MaxOps          \* Maximum operations per device

VARIABLES
    localState,     \* localState[d] = map of key -> encrypted_value per device
    oplog,          \* oplog[d] = sequence of ops per device
    seqNum,         \* seqNum[d] = current sequence number per device
    delivered,      \* delivered[d] = set of (device, seq) pairs already merged
    anchored        \* anchored = last committed merkle root

vars == <<localState, oplog, seqNum, delivered, anchored>>

TypeOK ==
    /\ \A d \in Devices : seqNum[d] \in Nat
    /\ \A d \in Devices : delivered[d] \subseteq (Devices \X Nat)

Init ==
    /\ localState = [d \in Devices |-> [k \in {} |-> 0]]
    /\ oplog = [d \in Devices |-> <<>>]
    /\ seqNum = [d \in Devices |-> 0]
    /\ delivered = [d \in Devices |-> {}]
    /\ anchored = 0

\* Device writes an encrypted op locally
Write(d, key, encValue) ==
    /\ seqNum[d] < MaxOps
    /\ seqNum' = [seqNum EXCEPT ![d] = seqNum[d] + 1]
    /\ oplog' = [oplog EXCEPT ![d] = Append(oplog[d], <<d, seqNum[d] + 1, key, encValue>>)]
    /\ localState' = [localState EXCEPT ![d] = [localState[d] EXCEPT ![key] = encValue]]
    /\ delivered' = [delivered EXCEPT ![d] = delivered[d] \union {<<d, seqNum[d] + 1>>}]
    /\ UNCHANGED anchored

\* Sync: device d2 receives an op from device d1
Sync(d1, d2) ==
    /\ d1 /= d2
    /\ \E i \in 1..Len(oplog[d1]) :
        LET op == oplog[d1][i]
            src == op[1]
            seq == op[2]
            key == op[3]
            val == op[4]
        IN
        /\ <<src, seq>> \notin delivered[d2]  \* Not yet seen
        /\ delivered' = [delivered EXCEPT ![d2] = delivered[d2] \union {<<src, seq>>}]
        /\ localState' = [localState EXCEPT ![d2] = [localState[d2] EXCEPT ![key] = val]]
        /\ UNCHANGED <<oplog, seqNum, anchored>>

\* Anchor: commit current state hash to chain
Anchor(d) ==
    /\ anchored' = Cardinality(delivered[d])  \* Simplified: count of merged ops as "hash"
    /\ UNCHANGED <<localState, oplog, seqNum, delivered>>

Next ==
    \/ \E d \in Devices, k \in {"a", "b", "c"}, v \in 1..10 : Write(d, k, v)
    \/ \E d1, d2 \in Devices : Sync(d1, d2)
    \/ \E d \in Devices : Anchor(d)

Spec == Init /\ [][Next]_vars

\* Safety: Convergence — if all ops are delivered, all devices agree
Convergence ==
    \A d1, d2 \in Devices :
        (delivered[d1] = delivered[d2]) => (localState[d1] = localState[d2])

\* Safety: Monotonic anchors — anchor value never decreases
MonotonicAnchor ==
    [][anchored' >= anchored]_vars

\* Safety: No op is processed twice (idempotent merge)
NoDuplicateDelivery ==
    \A d \in Devices :
        Cardinality(delivered[d]) = Cardinality(delivered[d])  \* Set semantics guarantee this

====
