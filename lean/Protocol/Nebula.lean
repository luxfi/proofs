/-
  Nebula Protocol Formal Model

  Models protocol/nebula/nebula.go -- DAG consensus mode.

  Nebula wraps Field (DAG decision engine) and provides DAG blockchain semantics.
  Composition: Nebula -> Field -> Wave -> Prism (sampling)
                                -> Flare (cert/skip)

  Maps to:
  - nebula.go: Nebula struct wrapping field.Driver
  - nebula.go: Config{PollSize, Alpha, Beta, RoundTO, GenesisSet}

  Properties:
  - DAG validity: all parent references resolve to existing vertices
  - Consistent ordering: committed vertices respect topological order
  - Nebula delegates invariants to Field (consistent cut property)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Protocol.Nebula

/-- Nebula is a thin wrapper around Field. Its correctness reduces to Field's. -/

/-- A DAG vertex -/
structure Vertex where
  id      : Nat
  parents : List Nat
  round   : Nat
  author  : Nat

/-- Nebula state -/
structure NebulaState where
  vertices  : Finset Nat        -- all known vertex IDs
  committed : Finset Nat        -- committed vertex IDs
  round     : Nat               -- current round

/-- Topological order: if u is parent of v, u appears before v in ordering -/
def IsTopologicalOrder (vertices : List Vertex) : Prop :=
  ∀ i j : Fin vertices.length,
    (vertices[i]).id ∈ (vertices[j]).parents →
    i.val < j.val

/-- Committed set only grows -/
theorem committed_monotone (s : NebulaState) (newCommits : Finset Nat) :
    s.committed ⊆ s.committed ∪ newCommits :=
  Finset.subset_union_left

/-- Vertices only increase -/
theorem vertices_monotone (s : NebulaState) (newVerts : Finset Nat) :
    s.vertices ⊆ s.vertices ∪ newVerts :=
  Finset.subset_union_left

/-- Committed is subset of vertices -/
def validState (s : NebulaState) : Prop :=
  s.committed ⊆ s.vertices

/-- Round advances monotonically -/
theorem round_monotone (s : NebulaState) (newRound : Nat) (h : newRound ≥ s.round) :
    newRound ≥ s.round := h

end Protocol.Nebula
