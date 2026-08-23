import Mathlib.Tactic
import TuzaRankFour.Packing

/-!
# Triangle-support reduction

The triangle support retains precisely the graph edges that occur in a
triangle.  It has the same triangle hypergraph as the original graph, hence
the same triangle packing and transversal numbers.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spanning triangle support of `G`.  Isolated vertices remain in the
carrier; they are removed separately when an order bound is required. -/
noncomputable def triangleSupport (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := ∃ t ∈ G.triangles, u ∈ t ∧ v ∈ t ∧ u ≠ v
  symm.symm := by
    rintro u v ⟨t, ht, hu, hv, huv⟩
    exact ⟨t, ht, hv, hu, huv.symm⟩
  loopless.irrefl := by
    rintro u ⟨t, ht, hu, hv, huu⟩
    exact huu rfl

@[simp]
theorem triangleSupport_adj_iff (G : SimpleGraph V) {u v : V} :
    G.triangleSupport.Adj u v ↔
      ∃ t ∈ G.triangles, u ∈ t ∧ v ∈ t ∧ u ≠ v :=
  Iff.rfl

theorem triangleSupport_le (G : SimpleGraph V) : G.triangleSupport ≤ G := by
  intro u v huv
  obtain ⟨t, ht, hu, hv, huvNe⟩ := huv
  have htClique : G.IsNClique 3 t := by
    simpa [triangles] using ht
  exact htClique.isClique hu hv huvNe

/-- The vertices that occur in at least one triangle of `G`. -/
noncomputable def triangleSupportVertices (G : SimpleGraph V) : Finset V := by
  classical
  exact G.triangles.biUnion id

@[simp]
theorem mem_triangleSupportVertices_iff (G : SimpleGraph V) {v : V} :
    v ∈ G.triangleSupportVertices ↔
      ∃ t ∈ G.triangles, v ∈ t := by
  classical
  simp [triangleSupportVertices]

/-- The graph-theoretic support of the spanning triangle-support graph is
exactly the union of the vertices of the original triangles. -/
theorem support_triangleSupport (G : SimpleGraph V) :
    G.triangleSupport.support =
      (G.triangleSupportVertices : Set V) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hvw⟩ := G.triangleSupport.mem_support.mp hv
    obtain ⟨t, ht, hvt, hwt, hvwNe⟩ := hvw
    exact G.mem_triangleSupportVertices_iff.mpr ⟨t, ht, hvt⟩
  · intro hv
    obtain ⟨t, ht, hvt⟩ := G.mem_triangleSupportVertices_iff.mp hv
    have htClique : G.IsNClique 3 t := by
      simpa [triangles] using ht
    have htCard := htClique.card_eq
    have hother : ∃ w ∈ t, w ≠ v := by
      by_contra h
      push Not at h
      have hsub : t ⊆ {v} := by
        intro w hw
        simp [h w hw]
      have hcard := Finset.card_le_card hsub
      simp at hcard
      omega
    obtain ⟨w, hwt, hwv⟩ := hother
    exact G.triangleSupport.mem_support.mpr
      ⟨w, ⟨t, ht, hvt, hwt, hwv.symm⟩⟩

/-- The carrier obtained by deleting vertices outside the triangle support. -/
abbrev TriangleSupportVertex (G : SimpleGraph V) :=
  {v : V // v ∈ G.triangleSupportVertices}

/-- The triangle support with vertices outside it removed. -/
noncomputable def triangleCore (G : SimpleGraph V) :
    SimpleGraph G.TriangleSupportVertex :=
  G.triangleSupport.induce (G.triangleSupportVertices : Set V)

@[simp]
theorem card_triangleSupportVertex (G : SimpleGraph V) :
    Fintype.card G.TriangleSupportVertex = G.triangleSupportVertices.card := by
  classical
  exact Fintype.card_coe _

/-- Removing edges outside triangles does not remove or create a triangle. -/
@[simp]
theorem triangles_triangleSupport (G : SimpleGraph V) :
    G.triangleSupport.triangles = G.triangles := by
  classical
  ext t
  simp only [triangles, mem_cliqueFinset_iff]
  constructor
  · intro ht
    refine ⟨?_, ht.card_eq⟩
    intro u hu v hv huv
    obtain ⟨s, hs, hsu, hsv, _⟩ := ht.isClique hu hv huv
    have hsClique : G.IsNClique 3 s := by
      simpa [triangles] using hs
    exact hsClique.isClique hsu hsv huv
  · intro ht
    refine ⟨?_, ht.card_eq⟩
    intro u hu v hv huv
    exact ⟨t, by simpa [triangles] using ht, hu, hv, huv⟩

theorem isTrianglePacking_triangleSupport_iff
    (G : SimpleGraph V) (P : Finset (Finset V)) :
    G.triangleSupport.IsTrianglePacking P ↔ G.IsTrianglePacking P := by
  classical
  simp only [IsTrianglePacking, G.triangles_triangleSupport]

/-- The triangle support has exactly the original packing number. -/
@[simp]
theorem trianglePackingNumber_triangleSupport (G : SimpleGraph V) :
    G.triangleSupport.trianglePackingNumber = G.trianglePackingNumber := by
  classical
  simp only [trianglePackingNumber, G.isTrianglePacking_triangleSupport_iff]

private theorem mem_triangleSupport_edges_of_subset_triangle
    (G : SimpleGraph V) {e t : Finset V}
    (ht : t ∈ G.triangleSupport.triangles)
    (het : e ⊆ t) (hecard : e.card = 2) :
    e ∈ G.triangleSupport.edges := by
  classical
  have htClique : G.triangleSupport.IsNClique 3 t := by
    simpa [triangles] using ht
  rw [edges, mem_cliqueFinset_iff]
  exact ⟨htClique.isClique.subset (by simpa using het), hecard⟩

/-- Intersecting a transversal with the support edges preserves the
transversal property and cannot increase its size. -/
theorem restrict_transversal_to_triangleSupport
    (G : SimpleGraph V) {C : Finset (Finset V)}
    (hC : G.IsTriangleTransversal C) :
    G.triangleSupport.IsTriangleTransversal
      (C ∩ G.triangleSupport.edges) ∧
      (C ∩ G.triangleSupport.edges).card ≤ C.card := by
  classical
  constructor
  · constructor
    · exact Finset.inter_subset_right
    · intro t ht
      have htG : t ∈ G.triangles := by simpa using ht
      obtain ⟨e, heC, het⟩ := hC.2 htG
      have heG := hC.1 heC
      have heCard : e.card = 2 := by
        have heClique : G.IsNClique 2 e := by
          simpa [edges] using heG
        exact heClique.card_eq
      have heSupport : e ∈ G.triangleSupport.edges :=
        mem_triangleSupport_edges_of_subset_triangle G ht het heCard
      exact ⟨e, Finset.mem_inter.mpr ⟨heC, heSupport⟩, het⟩
  · exact Finset.card_le_card Finset.inter_subset_left

/-- Every support transversal is also a transversal of the original graph. -/
theorem isTriangleTransversal_of_triangleSupport
    (G : SimpleGraph V) {C : Finset (Finset V)}
    (hC : G.triangleSupport.IsTriangleTransversal C) :
    G.IsTriangleTransversal C := by
  classical
  constructor
  · intro e he
    have heSupport := hC.1 he
    have heClique : G.triangleSupport.IsNClique 2 e := by
      simpa [edges] using heSupport
    rw [edges, mem_cliqueFinset_iff]
    exact ⟨heClique.isClique.mono G.triangleSupport_le, heClique.card_eq⟩
  · intro t ht
    exact hC.2 (by simpa using ht)

/-- The triangle support has exactly the original transversal number. -/
@[simp]
theorem triangleTransversalNumber_triangleSupport (G : SimpleGraph V) :
    G.triangleSupport.triangleTransversalNumber =
      G.triangleTransversalNumber := by
  apply le_antisymm
  · obtain ⟨C, hC, hcard⟩ := G.exists_min_triangleTransversal
    obtain ⟨hC', hcard'⟩ := G.restrict_transversal_to_triangleSupport hC
    exact (G.triangleSupport.triangleTransversalNumber_le_card hC').trans
      (hcard'.trans_eq hcard)
  · obtain ⟨C, hC, hcard⟩ := G.triangleSupport.exists_min_triangleTransversal
    exact (G.triangleTransversalNumber_le_card
      (G.isTriangleTransversal_of_triangleSupport hC)).trans_eq hcard

end SimpleGraph
