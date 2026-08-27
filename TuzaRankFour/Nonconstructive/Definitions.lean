import Mathlib.Tactic
import TuzaRankFour.Packing

/-!
# Generic definitions for the nonconstructive Tuza route

This file is independent of the rank-four finite endpoint.  It fixes the
literal finite-simple-graph notions used by the all-rank reduction route:
edge deletion, exact packing-rank blockers, strength-two reducers, and the
Tuza inequality itself.

Deleted edges use the repository's existing `Finset (Finset V)` ground-edge
representation.  An `ExactRankBlocker` requires every deleted object to be an
actual edge of the source graph; arbitrary non-edge finsets are therefore not
silently treated as resources.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete the actual ground edges listed in `C` from `G`.

The definition accepts a `Finset (Finset V)` so it composes directly with
`IsTriangleTransversal`.  Mathematical blocker predicates below additionally
require `C ⊆ G.edges`, which rules out malformed resources. -/
noncomputable def deleteEdgeFinset (G : SimpleGraph V)
    (C : Finset (Finset V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ({u, v} : Finset V) ∉ C
  symm.symm := by
    rintro u v ⟨huv, hC⟩
    exact ⟨huv.symm, by simpa [Finset.pair_comm] using hC⟩
  loopless.irrefl := by
    rintro u ⟨huu, _⟩
    exact G.loopless.irrefl u huu

@[simp]
theorem deleteEdgeFinset_adj_iff (G : SimpleGraph V)
    (C : Finset (Finset V)) {u v : V} :
    (G.deleteEdgeFinset C).Adj u v ↔
      G.Adj u v ∧ ({u, v} : Finset V) ∉ C :=
  Iff.rfl

/-- Edge deletion only removes source edges. -/
theorem deleteEdgeFinset_le (G : SimpleGraph V) (C : Finset (Finset V)) :
    G.deleteEdgeFinset C ≤ G := by
  intro u v huv
  exact huv.1

/-- Every residual ground edge is an edge of the source graph. -/
theorem edges_deleteEdgeFinset_subset (G : SimpleGraph V)
    (C : Finset (Finset V)) :
    (G.deleteEdgeFinset C).edges ⊆ G.edges := by
  classical
  intro e he
  have heClique : (G.deleteEdgeFinset C).IsNClique 2 e := by
    simpa [edges] using he
  rw [edges, mem_cliqueFinset_iff]
  exact ⟨heClique.isClique.mono (G.deleteEdgeFinset_le C), heClique.card_eq⟩

/-- A source triangle avoiding every listed deleted edge survives deletion. -/
theorem mem_triangles_deleteEdgeFinset_of_forall_not_subset
    (G : SimpleGraph V) (C : Finset (Finset V)) {t : Finset V}
    (ht : t ∈ G.triangles)
    (havoid : ∀ e ∈ C, ¬ e ⊆ t) :
    t ∈ (G.deleteEdgeFinset C).triangles := by
  classical
  have htClique : G.IsNClique 3 t := by
    simpa [triangles] using ht
  rw [triangles, mem_cliqueFinset_iff]
  refine ⟨?_, htClique.card_eq⟩
  intro u hu v hv huv
  refine ⟨htClique.isClique hu hv huv, ?_⟩
  intro hpair
  apply havoid {u, v} hpair
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hu
  · exact hv

/-- `G` satisfies the integral Tuza inequality. -/
def SatisfiesTuza (G : SimpleGraph V) : Prop :=
  G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber

/-- Deleting `C` lowers the triangle-packing number by exactly `d`.

The additive equation is intentional: it records exact damage without using
truncated natural-number subtraction. -/
structure IsExactRankBlocker (G : SimpleGraph V)
    (C : Finset (Finset V)) (d : ℕ) : Prop where
  edges_subset : C ⊆ G.edges
  rank_eq :
    (G.deleteEdgeFinset C).trianglePackingNumber + d =
      G.trianglePackingNumber

/-- A positive exact-rank blocker whose cost is at most twice its damage. -/
structure IsTuzaReducer (G : SimpleGraph V)
    (C : Finset (Finset V)) (d : ℕ) : Prop
    extends G.IsExactRankBlocker C d where
  damage_pos : 0 < d
  card_le : C.card ≤ 2 * d

/-- `G` has some positive strength-two exact-rank reduction. -/
def HasTuzaReducer (G : SimpleGraph V) : Prop :=
  ∃ C : Finset (Finset V), ∃ d : ℕ, G.IsTuzaReducer C d

/-- Every positive-rank graph on `V` admits a positive strength-two reducer.

This is deliberately a named conditional hypothesis, not an axiom or a
claimed theorem.  The all-rank contact route seeks a source-level structural
theorem strong enough to inhabit it. -/
def HasUnavoidableTuzaReduction (V : Type*)
    [Fintype V] [DecidableEq V] : Prop :=
  ∀ G : SimpleGraph V,
    0 < G.trianglePackingNumber → G.HasTuzaReducer

end SimpleGraph
