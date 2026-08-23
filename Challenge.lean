import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Tuza's conjecture for packing number at most four

An edge is represented by its two endpoints and a triangle by its three
vertices. The definitions below are duplicated in the proof development so
that Comparator can check both their statements and the theorem independently.
-/

namespace SimpleGraph

/-- The finite set of triangles of `G`, represented by their three vertices. -/
noncomputable def triangles {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact G.cliqueFinset 3

/-- The finite set of edges of `G`, represented by their two endpoints. -/
noncomputable def edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact G.cliqueFinset 2

/-- `P` is a family of pairwise edge-disjoint triangles of `G`. -/
noncomputable def IsTrianglePacking {V : Type*} [Fintype V]
    (G : SimpleGraph V) (P : Finset (Finset V)) : Prop := by
  classical
  exact P ⊆ G.triangles ∧
    ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → (s ∩ t).card ≤ 1

/-- `C` is a set of graph edges meeting every triangle of `G`. -/
noncomputable def IsTriangleTransversal {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : Finset (Finset V)) : Prop := by
  classical
  exact C ⊆ G.edges ∧
    ∀ ⦃t⦄, t ∈ G.triangles → ∃ e ∈ C, e ⊆ t

/-- The largest cardinality of a family of pairwise edge-disjoint triangles. -/
noncomputable def trianglePackingNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter G.IsTrianglePacking).sup Finset.card

/-- The least cardinality of a set of graph edges meeting every triangle. -/
noncomputable def triangleTransversalNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ C : Finset (Finset V),
    G.IsTriangleTransversal C ∧ C.card = n}

/-- Every finite simple graph with triangle-packing number at most four has an
edge triangle transversal of size at most twice its packing number. -/
theorem tuza_rank_four {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hν : G.trianglePackingNumber ≤ 4) :
    G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber := by
  sorry

end SimpleGraph
