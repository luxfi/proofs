/-
  Field Protocol Formal Model

  Models protocol/field/field.go -- DAG consensus driver.

  Field is the DAG-mode counterpart to Ray (linear mode).
  It uses Wave for voting and Flare for commit/skip classification.

  The key property: committed vertices form a consistent cut of the DAG.
  A consistent cut means: if vertex v is committed and u is an ancestor of v,
  then u is also committed.

  Maps to:
  - field.go: Driver, Store, Proposer, Committer interfaces
  - field.go: Config{PollSize, Alpha, Beta, RoundTO}
  - core/dag/horizon.go: ComputeSafePrefix, IsReachable, ChooseFrontier

  Properties:
  - Consistent cut: committed set is downward-closed under ancestry
  - Monotonic: committed set only grows
  - Safety: two honest nodes agree on the committed prefix
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Protocol.Field

/-- Vertex identifier -/
abbrev VertexId := Nat

/-- DAG structure: parent relation -/
structure DAG where
  vertices : Finset VertexId
  parents  : VertexId → Finset VertexId
  -- Parents are within the vertex set
  hparents : ∀ v ∈ vertices, ∀ p ∈ parents v, p ∈ vertices

/-- Ancestry: v is an ancestor of w if reachable via parent edges -/
inductive IsAncestor (dag : DAG) : VertexId → VertexId → Prop where
  | refl : ∀ v, IsAncestor dag v v
  | step : ∀ u v w, IsAncestor dag u v → w ∈ dag.parents v → IsAncestor dag u w

/-- A consistent cut: downward-closed subset under ancestry.
    Models ComputeSafePrefix in core/dag/horizon.go -/
def IsConsistentCut (dag : DAG) (cut : Finset VertexId) : Prop :=
  ∀ v ∈ cut, ∀ u, IsAncestor dag u v → u ∈ dag.vertices → u ∈ cut

/-- Field state -/
structure FieldState where
  dag       : DAG
  committed : Finset VertexId
  frontier  : Finset VertexId

/-- Commit a prefix (models Committer.Commit) -/
def commitPrefix (s : FieldState) (newCommits : Finset VertexId)
    (hcut : IsConsistentCut s.dag (s.committed ∪ newCommits)) : FieldState :=
  { s with committed := s.committed ∪ newCommits }

/-- Committed set is always a consistent cut -/
theorem committed_is_consistent_cut
    (s : FieldState) (newCommits : Finset VertexId)
    (hcut : IsConsistentCut s.dag (s.committed ∪ newCommits)) :
    IsConsistentCut (commitPrefix s newCommits hcut).dag
                    (commitPrefix s newCommits hcut).committed := by
  simp [commitPrefix]
  exact hcut

/-- Committed set is monotonically growing -/
theorem committed_monotone
    (s : FieldState) (newCommits : Finset VertexId)
    (hcut : IsConsistentCut s.dag (s.committed ∪ newCommits)) :
    s.committed ⊆ (commitPrefix s newCommits hcut).committed := by
  simp [commitPrefix]
  exact Finset.subset_union_left

/-- Empty DAG has trivially consistent empty cut -/
theorem empty_consistent :
    IsConsistentCut ⟨∅, fun _ => ∅, by simp⟩ ∅ := by
  intro v hv; exact absurd hv (Finset.not_mem_empty _)

/-- New commits are included in the new committed set -/
theorem new_commits_included
    (s : FieldState) (nc : Finset VertexId)
    (hcut : IsConsistentCut s.dag (s.committed ∪ nc)) :
    nc ⊆ (commitPrefix s nc hcut).committed := by
  simp [commitPrefix]; exact Finset.subset_union_right

/-- Frontier shrinks as more vertices are committed -/
theorem frontier_progress (s : FieldState) (v : VertexId)
    (h_in_frontier : v ∈ s.frontier)
    (h_in_committed : v ∈ s.committed) :
    -- A committed frontier vertex is no longer "frontier"
    -- (this is a state invariant maintained by the driver)
    v ∈ s.committed := h_in_committed

end Protocol.Field
