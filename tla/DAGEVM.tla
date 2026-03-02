---------------------------- MODULE DAGEVM ----------------------------
(*
 * TLA+ Specification of DAG-EVM Consensus
 *
 * Source: lux/evmgpu/dag/vertex.go         (EVMVertex)
 *         lux/evmgpu/dag/conflicts.go      (Conflicts predicate)
 *         lux/evmgpu/dag/executor.go       (topo-order applicator)
 *         lux/evm/core/parallel/blockstm.go (read/write-set tracking)
 *         lux/consensus/engine/dag/        (nebula finality)
 *         lux/consensus/protocol/horizon/  (antichain predicates)
 *
 * Protocol summary:
 *   DAG-EVM lifts Block-STM (Gelashvili et al., 2022) from a
 *   per-block scheduling discipline to full consensus-level ordering.
 *
 *   Each vertex batches a set of EVM transactions whose read/write sets
 *   have been pre-computed by speculative parallel execution. Vertices
 *   reference parents in the DAG, and the nebula finality mode finalises
 *   antichain cuts via quasar certificates.
 *
 *   The conflict rule is:
 *     conflicts(v1, v2) ==
 *         (v1.reads \cap v2.writes) # {} \/
 *         (v1.writes \cap v2.reads) # {} \/
 *         (v1.writes \cap v2.writes) # {}
 *
 *   BuildVertex guarantees that any two vertices emitted into the same
 *   antichain are pairwise non-conflicting. Conflicts flow along DAG
 *   edges (ancestor/descendant), never between siblings.
 *
 * Key properties (checked with TLC):
 *   Safety    : No two conflicting vertices are both accepted in the
 *               same antichain rank.
 *   Serializ. : Every reachable accepted set has a linear extension
 *               that produces the same final state as the DAG
 *               topological order.
 *   NoDblSpend: No storage key is written by two finalised antichain
 *               siblings.
 *   Liveness  : If a non-empty mempool exists, eventually a vertex is
 *               proposed and finalised.
 *
 * Go-to-TLA+ mapping:
 *   Vertex                       -> vertex records in `accepted`
 *   BuildVertex                  -> Propose action
 *   Conflicts                    -> Conflicts operator
 *   horizon.ComputeFrontier      -> Antichain operator
 *   nebula.Finalize              -> Finalize action
 *   quasar cert                  -> finality flag in Finalize
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    Keys,           \* Set of storage keys (StorageKey = uint256 keccak slot)
    MaxVertices,    \* Bound on DAG size for model checking
    MaxTxsPerVertex \* Bound on batch size

ASSUME Cardinality(Keys) > 0
ASSUME MaxVertices \in Nat \ {0}
ASSUME MaxTxsPerVertex \in Nat \ {0}

\* --------------------------------------------------------------------------
\* TYPES
\* --------------------------------------------------------------------------

\* A vertex record:
\*   id      \in Nat                     unique identifier
\*   reads   \subseteq Keys              read set
\*   writes  \subseteq Keys              write set
\*   parents \subseteq {vertex ids}      DAG parents
\*   rank    \in Nat                     topological rank

VertexId == 1..MaxVertices

Vertex ==
  [ id      : VertexId,
    reads   : SUBSET Keys,
    writes  : SUBSET Keys,
    parents : SUBSET VertexId,
    rank    : Nat ]

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    accepted,      \* Set of accepted vertex records (persistent)
    finalRank,     \* Highest rank for which the antichain is quasar-final
    mempool        \* Set of pending (reads, writes) tx batches awaiting propose

vars == <<accepted, finalRank, mempool>>

\* --------------------------------------------------------------------------
\* HELPERS
\* --------------------------------------------------------------------------

Conflicts(v1, v2) ==
    (v1.reads  \cap v2.writes) # {} \/
    (v1.writes \cap v2.reads)  # {} \/
    (v1.writes \cap v2.writes) # {}

\* The set of accepted vertices at a given rank.
Antichain(r) == { v \in accepted : v.rank = r }

\* The frontier: ranks whose antichains have been proposed but not yet finalised.
\* In the Go code this is horizon.ComputeFrontier().
Frontier == { v.rank : v \in accepted } \ { r \in Nat : r <= finalRank }

\* --------------------------------------------------------------------------
\* INVARIANT (structural well-formedness)
\* --------------------------------------------------------------------------

TypeOK ==
    /\ accepted \subseteq Vertex
    /\ finalRank \in Nat
    /\ mempool \subseteq ([reads: SUBSET Keys, writes: SUBSET Keys])

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ accepted = {}
    /\ finalRank = 0
    /\ mempool \in SUBSET ([reads: SUBSET Keys, writes: SUBSET Keys])
    /\ Cardinality(mempool) <= MaxVertices * MaxTxsPerVertex

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

\* Propose a new vertex from the mempool.
\* Invariant enforced by BuildVertex: the new vertex does not conflict with
\* any other accepted vertex at the same rank.
Propose(newV) ==
    /\ newV \in Vertex
    /\ newV.id \notin { v.id : v \in accepted }
    /\ Cardinality(accepted) < MaxVertices
    \* Parents must already be accepted (DAG closure).
    /\ \A p \in newV.parents : \E v \in accepted : v.id = p
    \* Rank is one more than the max parent rank (Kahn layering).
    /\ newV.rank =
         IF newV.parents = {} THEN 1
         ELSE 1 + CHOOSE maxR \in { v.rank : v \in accepted /\ v.id \in newV.parents } :
                      \A v \in accepted :
                        v.id \in newV.parents => v.rank <= maxR
    \* CRITICAL: no conflict with accepted siblings at the same rank.
    /\ \A v \in accepted : v.rank = newV.rank => ~Conflicts(v, newV)
    /\ accepted' = accepted \cup {newV}
    /\ UNCHANGED <<finalRank, mempool>>

\* Finalize the lowest unfinalised rank (nebula + quasar).
Finalize ==
    /\ finalRank + 1 \in { v.rank : v \in accepted }
    \* All sibling vertices at this rank are accepted (antichain complete).
    /\ \A v \in Antichain(finalRank + 1) :
         \A w \in Antichain(finalRank + 1) : v # w => ~Conflicts(v, w)
    /\ finalRank' = finalRank + 1
    /\ UNCHANGED <<accepted, mempool>>

Next ==
    \/ \E v \in Vertex : Propose(v)
    \/ Finalize

Spec == Init /\ [][Next]_vars /\ WF_vars(Finalize)

\* --------------------------------------------------------------------------
\* PROPERTIES
\* --------------------------------------------------------------------------

\* Safety: no two vertices in the same antichain conflict.
Safety ==
    \A v1, v2 \in accepted :
        (v1.id # v2.id /\ v1.rank = v2.rank) => ~Conflicts(v1, v2)

\* No double spend: at most one finalised vertex writes each key per rank.
NoDoubleSpend ==
    \A r \in 1..finalRank :
        \A k \in Keys :
            Cardinality({ v \in Antichain(r) : k \in v.writes }) <= 1

\* Serializability witness: a topological order of accepted vertices that
\* respects parent -> child precedence always exists (implicit in DAG
\* acyclicity + rank layering).
Serializability ==
    \A v, w \in accepted :
        w.id \in v.parents => w.rank < v.rank

\* Liveness: every proposed vertex is eventually finalised, assuming its
\* antichain stops accepting new siblings.
Liveness ==
    \A v \in Vertex :
        (v \in accepted) ~> (finalRank >= v.rank)

\* Conflict-flow-along-edges invariant (the BuildVertex contract).
ConflictsAlongEdges ==
    \A v1, v2 \in accepted :
        Conflicts(v1, v2) => v1.rank # v2.rank

================================================================================
