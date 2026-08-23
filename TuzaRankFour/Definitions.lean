import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Triangle packings and edge transversals

The definitions in this file use finite vertex sets directly. An edge is a
two-element clique and a triangle is a three-element clique. Consequently two
triangles share an edge exactly when their vertex sets have intersection of
cardinality at least two.
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

/-- `P` is a triangle packing when all its members are triangles of `G` and
distinct members share no graph edge. -/
noncomputable def IsTrianglePacking {V : Type*} [Fintype V]
    (G : SimpleGraph V) (P : Finset (Finset V)) : Prop := by
  classical
  exact P ⊆ G.triangles ∧
    ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → (s ∩ t).card ≤ 1

/-- `C` is an edge triangle transversal when every member of `C` is an edge
of `G` and every triangle of `G` contains a member of `C`. -/
noncomputable def IsTriangleTransversal {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : Finset (Finset V)) : Prop := by
  classical
  exact C ⊆ G.edges ∧
    ∀ ⦃t⦄, t ∈ G.triangles → ∃ e ∈ C, e ⊆ t

/-- The triangle-packing number `ν(G)`: the largest cardinality of a family
of pairwise edge-disjoint triangles in `G`. -/
noncomputable def trianglePackingNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter G.IsTrianglePacking).sup Finset.card

/-- The edge triangle-transversal number `τ(G)`: the least cardinality of a
set of graph edges that meets every triangle. -/
noncomputable def triangleTransversalNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ C : Finset (Finset V),
    G.IsTriangleTransversal C ∧ C.card = n}

end SimpleGraph
