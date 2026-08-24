import TuzaRankFour.CrownExtraction

/-!
# Independence of the residual zero-vertex domain

The discharge leaves possible zeros only outside the packing or among the
vertices private to excellent packing triangles.  This file proves that the
union of those two classes is independent.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every endpoint of a labelled packing edge belongs to the support of the
packing. -/
theorem labelledPackingVertices_subset_triangleFamilyVertexSupport
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    G.labelledPackingVertices S ⊆ triangleFamilyVertexSupport S := by
  classical
  intro v hv
  obtain ⟨e, heLabelled, hve⟩ :=
    (G.mem_labelledPackingVertices_iff).mp hv
  obtain ⟨t, htS, heSub, _⟩ := mem_triangleFamilyEdges_iff.mp
    (G.mem_labelledPackingEdges_iff.mp heLabelled).1
  exact Finset.mem_biUnion.mpr ⟨t, htS, heSub hve⟩

omit [Fintype V] in
/-- A two-subset of a three-set containing two distinct specified vertices
contains at least one of those vertices. -/
theorem two_subset_three_meets_pair
    {t e : Finset V} {u v : V}
    (htCard : t.card = 3) (heCard : e.card = 2) (heSub : e ⊆ t)
    (hut : u ∈ t) (hvt : v ∈ t) (huv : u ≠ v) :
    u ∈ e ∨ v ∈ e := by
  classical
  by_contra hNeither
  push Not at hNeither
  have hsub : e ⊆ (t.erase u).erase v := by
    intro z hze
    exact Finset.mem_erase.mpr
      ⟨fun hzv ↦ hNeither.2 (hzv ▸ hze),
        Finset.mem_erase.mpr
          ⟨fun hzu ↦ hNeither.1 (hzu ▸ hze), heSub hze⟩⟩
  have hvErase : v ∈ t.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvt⟩
  have hcard : ((t.erase u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hvErase,
      Finset.card_erase_of_mem hut, htCard]
  have := Finset.card_le_card hsub
  omega

/-- Vertices outside a support-maximal packing together with the vertices
private to excellent packed triangles form an independent set. -/
theorem isIndepSet_outside_union_excellentResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hTriangleSupport : G.triangleSupport = G) :
    G.IsIndepSet
      ((outsidePackingVertices S ∪ G.excellentResidualVertices S : Finset V) :
        Set V) := by
  classical
  rw [G.isIndepSet_iff]
  intro u hu v hv huv huvAdj
  have huNotLabelled : u ∉ G.labelledPackingVertices S := by
    intro huLabelled
    have huSupport := G.labelledPackingVertices_subset_triangleFamilyVertexSupport
      S huLabelled
    rcases Finset.mem_union.mp hu with huOutside | huExcellent
    · exact (mem_outsidePackingVertices_iff.mp huOutside) huSupport
    · exact (G.mem_excellentResidualVertices_iff.mp huExcellent).2.1 huLabelled
  have hvNotLabelled : v ∉ G.labelledPackingVertices S := by
    intro hvLabelled
    have hvSupport := G.labelledPackingVertices_subset_triangleFamilyVertexSupport
      S hvLabelled
    rcases Finset.mem_union.mp hv with hvOutside | hvExcellent
    · exact (mem_outsidePackingVertices_iff.mp hvOutside) hvSupport
    · exact (G.mem_excellentResidualVertices_iff.mp hvExcellent).2.1 hvLabelled
  have huvSupport : G.triangleSupport.Adj u v := by
    rw [hTriangleSupport]
    exact huvAdj
  obtain ⟨r, hrTriangle, hur, hvr, _⟩ :=
    G.triangleSupport_adj_iff.mp huvSupport
  obtain ⟨q, hqS, hinterLower⟩ :=
    G.exists_two_le_card_inter_of_isSupportMaximalPacking hS hrTriangle
  obtain ⟨e, heInter⟩ : ∃ e, e ∈ (q ∩ r).powersetCard 2 :=
    Finset.powersetCard_nonempty.mpr hinterLower
  have heData := Finset.mem_powersetCard.mp heInter
  have heCard : e.card = 2 := heData.2
  have heSubQ : e ⊆ q := fun z hz ↦ (Finset.mem_inter.mp (heData.1 hz)).1
  have heSubR : e ⊆ r := fun z hz ↦ (Finset.mem_inter.mp (heData.1 hz)).2
  have heQ : e ∈ q.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨heSubQ, heCard⟩
  have heR : e ∈ r.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨heSubR, heCard⟩
  have heFamily : e ∈ triangleFamilyEdges S := by
    rw [mem_triangleFamilyEdges_iff]
    exact ⟨q, hqS, heSubQ, heCard⟩
  have hrCard : r.card = 3 := G.card_eq_three_of_mem_triangles hrTriangle
  have hAvoids : G.TriangleAvoidsPackingLabels S r := by
    refine ⟨hrTriangle, ?_⟩
    rw [Finset.disjoint_left]
    intro d hdR hdLabelled
    have hdData := Finset.mem_powersetCard.mp hdR
    rcases two_subset_three_meets_pair hrCard hdData.2 hdData.1
      hur hvr huv with hud | hvd
    · exact huNotLabelled ((G.mem_labelledPackingVertices_iff).mpr
        ⟨d, hdLabelled, hud⟩)
    · exact hvNotLabelled ((G.mem_labelledPackingVertices_iff).mpr
        ⟨d, hdLabelled, hvd⟩)
  have heNotLabelled : e ∉ G.labelledPackingEdges S := by
    exact Finset.disjoint_left.mp hAvoids.2 heR
  by_cases heuv : e = {u, v}
  · have huq : u ∈ q := heSubQ (by simpa [heuv])
    have hvq : v ∈ q := heSubQ (by simpa [heuv])
    have huExcellent : u ∈ G.excellentResidualVertices S := by
      rcases Finset.mem_union.mp hu with huOutside | huExcellent
      · exact (mem_outsidePackingVertices_iff.mp huOutside
          (Finset.mem_biUnion.mpr ⟨q, hqS, huq⟩)).elim
      · exact huExcellent
    have hqNotBad : q ∉ G.badPackingTriangles S := by
      intro hqBad
      exact (G.mem_excellentResidualVertices_iff.mp huExcellent).2.2.2
        (Finset.mem_biUnion.mpr ⟨q, hqBad, huq⟩)
    have hqGood : q ∈ G.goodPackingTriangles S := by
      have hpart : q ∈ G.goodPackingTriangles S ∨
          q ∈ G.badPackingTriangles S := by
        rw [← Finset.mem_union, G.good_union_bad_eq]
        exact hqS
      rcases hpart with hgood | hbad
      · exact hgood
      · exact (hqNotBad hbad).elim
    obtain ⟨d, hdLabelledInQ⟩ :=
      (G.mem_goodPackingTriangles_iff.mp hqGood).2
    have hdData := Finset.mem_inter.mp hdLabelledInQ
    have hqCard : q.card = 3 := G.card_eq_three_of_mem_triangles (hS.1.1 hqS)
    rcases two_subset_three_meets_pair hqCard
      (Finset.mem_powersetCard.mp hdData.1).2
      (Finset.mem_powersetCard.mp hdData.1).1 huq hvq huv with hud | hvd
    · exact huNotLabelled ((G.mem_labelledPackingVertices_iff).mpr
        ⟨d, hdData.2, hud⟩)
    · exact hvNotLabelled ((G.mem_labelledPackingVertices_iff).mpr
        ⟨d, hdData.2, hvd⟩)
  · have hmeet : u ∈ e ∨ v ∈ e :=
      two_subset_three_meets_pair hrCard heCard heSubR hur hvr huv
    obtain ⟨a, haV1, hae⟩ :
        ∃ a, a ∈ G.excellentResidualVertices S ∧ a ∈ e := by
      rcases hmeet with hue | hve
      · refine ⟨u, ?_, hue⟩
        rcases Finset.mem_union.mp hu with huOutside | huExcellent
        · exact (mem_outsidePackingVertices_iff.mp huOutside
            (Finset.mem_biUnion.mpr ⟨q, hqS, heSubQ hue⟩)).elim
        · exact huExcellent
      · refine ⟨v, ?_, hve⟩
        rcases Finset.mem_union.mp hv with hvOutside | hvExcellent
        · exact (mem_outsidePackingVertices_iff.mp hvOutside
            (Finset.mem_biUnion.mpr ⟨q, hqS, heSubQ hve⟩)).elim
        · exact hvExcellent
    have haq : a ∈ q := heSubQ hae
    have haData := G.mem_excellentResidualVertices_iff.mp haV1
    have hqNotBad : q ∉ G.badPackingTriangles S := by
      intro hqBad
      exact haData.2.2.2 (Finset.mem_biUnion.mpr ⟨q, hqBad, haq⟩)
    have hqGood : q ∈ G.goodPackingTriangles S := by
      have hpart : q ∈ G.goodPackingTriangles S ∨
          q ∈ G.badPackingTriangles S := by
        rw [← Finset.mem_union, G.good_union_bad_eq]
        exact hqS
      rcases hpart with hgood | hbad
      · exact hgood
      · exact (hqNotBad hbad).elim
    have hqExcellent : G.IsExcellentPackingTriangle S q := by
      by_contra hNotExcellent
      have hqPretty : q ∈ G.prettyGoodPackingTriangles S :=
        (G.mem_prettyGoodPackingTriangles_iff).mpr
          ⟨hqGood, hNotExcellent⟩
      exact haData.2.2.1
        (Finset.mem_biUnion.mpr ⟨q, hqPretty, haq⟩)
    exact hqExcellent.2 heQ heNotLabelled hAvoids heSubR

end SimpleGraph
