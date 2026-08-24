import Mathlib.Tactic
import TuzaRankFour.Parker
import TuzaRankFour.Reduction

/-!
# Triangle-isolated complete four-vertex blocks

This file formalizes the packing part of the exact reduction obtained by
deleting all six edges of a copy of `K₄` that shares no edge with a triangle
outside the copy.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A four-clique is triangle-isolated when every triangle containing an
edge of the clique is one of its four faces. -/
def IsTriangleIsolatedK4 (G : SimpleGraph V) (Q : Finset V) : Prop :=
  G.IsNClique 4 Q ∧
    ∀ ⦃t : Finset V⦄, t ∈ G.triangles →
      2 ≤ (t ∩ Q).card → t ⊆ Q

/-- Deleting one vertex from a four-clique leaves a triangular face. -/
theorem erase_mem_triangles_of_isNClique_four
    (G : SimpleGraph V) {Q : Finset V}
    (hQ : G.IsNClique 4 Q) {x : V} (hx : x ∈ Q) :
    Q.erase x ∈ G.triangles := by
  classical
  have hcard : (Q.erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hx, hQ.card_eq]
  have hface : G.IsNClique 3 (Q.erase x) :=
    ⟨hQ.isClique.subset (by simp), hcard⟩
  simpa [triangles] using hface

/-- Every triangle deleted with the internal edges of an isolated `K₄` is a
face of that `K₄`. -/
theorem subset_of_mem_triangles_not_mem_deleteEdgesWithin
    (G : SimpleGraph V) {Q t : Finset V}
    (hQ : G.IsTriangleIsolatedK4 Q)
    (ht : t ∈ G.triangles)
    (htDeleted : t ∉ (G.deleteEdgesWithin Q).triangles) :
    t ⊆ Q := by
  apply hQ.2 ht
  have hnot : ¬(t ∩ Q).card ≤ 1 := by
    intro hsmall
    exact htDeleted (G.mem_triangles_deleteEdgesWithin_iff.mpr ⟨ht, hsmall⟩)
  omega

omit [Fintype V] in
/-- Two distinct triangular faces of the same four-set share an edge. -/
theorem two_le_card_inter_of_three_subsets_of_four
    {Q q r : Finset V}
    (hQcard : Q.card = 4)
    (hqcard : q.card = 3) (hrcard : r.card = 3)
    (hqQ : q ⊆ Q) (hrQ : r ⊆ Q) :
    2 ≤ (q ∩ r).card := by
  have hunion : q ∪ r ⊆ Q := Finset.union_subset hqQ hrQ
  have hunionCard : (q ∪ r).card ≤ 4 := by
    simpa [hQcard] using Finset.card_le_card hunion
  have hinclusion := Finset.card_union_add_card_inter q r
  omega

/-- At most one member of a triangle packing can be deleted with the
internal edges of a triangle-isolated `K₄`. -/
theorem card_filter_not_mem_deleteEdgesWithin_triangles_le_one
    (G : SimpleGraph V) {Q : Finset V} {P : Finset (Finset V)}
    (hQ : G.IsTriangleIsolatedK4 Q)
    (hP : G.IsTrianglePacking P) :
    (P.filter fun t => t ∉ (G.deleteEdgesWithin Q).triangles).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro q r hq hr
  simp only [Finset.mem_filter] at hq hr
  by_contra hqr
  have hqSub : q ⊆ Q :=
    G.subset_of_mem_triangles_not_mem_deleteEdgesWithin hQ (hP.1 hq.1) hq.2
  have hrSub : r ⊆ Q :=
    G.subset_of_mem_triangles_not_mem_deleteEdgesWithin hQ (hP.1 hr.1) hr.2
  have hinter : 2 ≤ (q ∩ r).card :=
    two_le_card_inter_of_three_subsets_of_four hQ.1.card_eq
      (G.card_eq_three_of_mem_triangles (hP.1 hq.1))
      (G.card_eq_three_of_mem_triangles (hP.1 hr.1)) hqSub hrSub
  have hsmall := hP.2 hq.1 hr.1 hqr
  omega

/-- Deleting the six internal edges of a triangle-isolated `K₄` lowers the
triangle packing number by exactly one. -/
theorem trianglePackingNumber_eq_deleteEdgesWithin_add_one
    (G : SimpleGraph V) {Q : Finset V}
    (hQ : G.IsTriangleIsolatedK4 Q) :
    G.trianglePackingNumber =
      (G.deleteEdgesWithin Q).trianglePackingNumber + 1 := by
  classical
  apply le_antisymm
  · obtain ⟨P, hP, hPcard⟩ := G.exists_max_trianglePacking
    let P' := P.filter fun t => t ∈ (G.deleteEdgesWithin Q).triangles
    have hP' : (G.deleteEdgesWithin Q).IsTrianglePacking P' := by
      constructor
      · intro t ht
        exact (Finset.mem_filter.mp ht).2
      · intro q hq r hr hqr
        exact hP.2 (Finset.mem_filter.mp hq).1
          (Finset.mem_filter.mp hr).1 hqr
    have hgood : P'.card ≤
        (G.deleteEdgesWithin Q).trianglePackingNumber :=
      (G.deleteEdgesWithin Q).card_le_trianglePackingNumber hP'
    have hbad :
        (P.filter fun t => t ∉ (G.deleteEdgesWithin Q).triangles).card ≤ 1 :=
      G.card_filter_not_mem_deleteEdgesWithin_triangles_le_one hQ hP
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := P) (fun t => t ∈ (G.deleteEdgesWithin Q).triangles)
    change P'.card +
      (P.filter fun t => t ∉ (G.deleteEdgesWithin Q).triangles).card = P.card
      at hsplit
    omega
  · obtain ⟨P, hP, hPcard⟩ :=
      (G.deleteEdgesWithin Q).exists_max_trianglePacking
    have hQpos : 0 < Q.card := by simp [hQ.1.card_eq]
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hQpos
    let q := Q.erase x
    have hq : q ∈ G.triangles := by
      simpa [q] using G.erase_mem_triangles_of_isNClique_four hQ.1 hx
    have hPG : G.IsTrianglePacking P := by
      constructor
      · intro t ht
        exact (G.mem_triangles_deleteEdgesWithin_iff.mp (hP.1 ht)).1
      · exact hP.2
    have hqSub : q ⊆ Q := by
      intro v hv
      change v ∈ Q.erase x at hv
      exact (Finset.mem_erase.mp hv).2
    have hcompat : ∀ ⦃t⦄, t ∈ P → (t ∩ q).card ≤ 1 := by
      intro t ht
      have htQ := (G.mem_triangles_deleteEdgesWithin_iff.mp (hP.1 ht)).2
      have hsub : t ∩ q ⊆ t ∩ Q := by
        intro v hv
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hv).1,
            hqSub (Finset.mem_inter.mp hv).2⟩
      exact (Finset.card_le_card hsub).trans htQ
    have hqNot : q ∉ P := by
      intro hqP
      have hsmall := hcompat hqP
      have hqCard := G.card_eq_three_of_mem_triangles hq
      simpa [hqCard] using hsmall
    have hinsert := G.isTrianglePacking_insert hPG hq hcompat
    have hbound := G.card_le_trianglePackingNumber hinsert
    rw [Finset.card_insert_of_notMem hqNot, hPcard] at hbound
    exact hbound

omit [Fintype V] in
/-- A three-subset of a four-set contains one part of any partition into two
two-subsets. -/
theorem subset_left_or_sdiff_subset_of_card_three_of_card_four
    {Q e t : Finset V}
    (hQcard : Q.card = 4) (heQ : e ⊆ Q) (hecard : e.card = 2)
    (htQ : t ⊆ Q) (htcard : t.card = 3) :
    e ⊆ t ∨ Q \ e ⊆ t := by
  classical
  let f := Q \ e
  have hfcard : f.card = 2 := by
    simp [f, Finset.card_sdiff_of_subset heQ, hQcard, hecard]
  by_contra h
  push Not at h
  obtain ⟨heNot, hfNot⟩ := h
  have hinter_le_one (a : Finset V) (hacard : a.card = 2)
      (haNot : ¬a ⊆ t) : (t ∩ a).card ≤ 1 := by
    have hinterSub : t ∩ a ⊆ a := Finset.inter_subset_right
    have hinterCard : (t ∩ a).card ≤ 2 := by
      simpa [hacard] using Finset.card_le_card hinterSub
    by_contra hlarge
    have hinterEqCard : (t ∩ a).card = a.card := by omega
    have hinterEq : t ∩ a = a :=
      Finset.eq_of_subset_of_card_le hinterSub (by omega)
    apply haNot
    intro v hv
    have : v ∈ t ∩ a := by simpa [hinterEq] using hv
    exact (Finset.mem_inter.mp this).1
  have heInter := hinter_le_one e hecard heNot
  have hfInter := hinter_le_one f hfcard hfNot
  have hpartition : e ∪ f = Q := by
    simpa [f, Finset.union_comm] using Finset.sdiff_union_of_subset heQ
  have htDecomp : t = (t ∩ e) ∪ (t ∩ f) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hvt
      have hvQ := htQ hvt
      have hvPartition : v ∈ e ∪ f := by simpa [hpartition] using hvQ
      rcases Finset.mem_union.mp hvPartition with hve | hvf
      · exact Or.inl ⟨hvt, hve⟩
      · exact Or.inr ⟨hvt, hvf⟩
    · rintro (⟨hvt, _⟩ | ⟨hvt, _⟩) <;> exact hvt
  have hcardUnion := Finset.card_union_le (t ∩ e) (t ∩ f)
  rw [← htDecomp, htcard] at hcardUnion
  omega

/-- The four faces of a four-clique have a transversal consisting of two
opposite internal edges. -/
theorem exists_two_edge_cover_of_four_clique
    (G : SimpleGraph V) {Q : Finset V}
    (hQ : G.IsNClique 4 Q) :
    ∃ H : Finset (Finset V),
      H ⊆ G.edges ∧ H.card ≤ 2 ∧
        ∀ ⦃t : Finset V⦄, t ⊆ Q → t.card = 3 →
          ∃ e ∈ H, e ⊆ t := by
  classical
  obtain ⟨e, heQ, hecard⟩ :=
    Finset.exists_subset_card_eq (s := Q) (n := 2) (by simp [hQ.card_eq])
  let f := Q \ e
  have hfQ : f ⊆ Q := Finset.sdiff_subset
  have hfcard : f.card = 2 := by
    simp [f, Finset.card_sdiff_of_subset heQ, hQ.card_eq, hecard]
  have heEdge : e ∈ G.edges := by
    rw [edges, mem_cliqueFinset_iff]
    exact ⟨hQ.isClique.subset (by simpa using heQ), hecard⟩
  have hfEdge : f ∈ G.edges := by
    rw [edges, mem_cliqueFinset_iff]
    exact ⟨hQ.isClique.subset (by simpa using hfQ), hfcard⟩
  refine ⟨{e, f}, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact heEdge
    · exact hfEdge
  · have hcard := Finset.card_insert_le e {f}
    simpa using hcard
  · intro t htQ htcard
    rcases subset_left_or_sdiff_subset_of_card_three_of_card_four
        hQ.card_eq heQ hecard htQ htcard with het | hft
    · exact ⟨e, by simp, het⟩
    · exact ⟨f, by simp [f], by simpa [f] using hft⟩

/-- Any edge transversal of a four-clique uses at least two edges internal to
the clique. -/
theorem two_le_card_filter_subset_of_four_clique
    (G : SimpleGraph V) {Q : Finset V} {C : Finset (Finset V)}
    (hQ : G.IsNClique 4 Q) (hC : G.IsTriangleTransversal C) :
    2 ≤ (C.filter fun e => e ⊆ Q).card := by
  classical
  by_contra hsmall
  have hcardLe : (C.filter fun e => e ⊆ Q).card ≤ 1 := by omega
  have hQpos : 0 < Q.card := by simp [hQ.card_eq]
  obtain ⟨y, hyQ⟩ := Finset.card_pos.mp hQpos
  have hfaceY := G.erase_mem_triangles_of_isNClique_four hQ hyQ
  obtain ⟨e, heC, heFaceY⟩ := hC.2 hfaceY
  have heQ : e ⊆ Q := heFaceY.trans (Finset.erase_subset y Q)
  have heFilter : e ∈ C.filter fun a => a ⊆ Q :=
    Finset.mem_filter.mpr ⟨heC, heQ⟩
  have heCard : e.card = 2 := by
    have heClique : G.IsNClique 2 e := by simpa [edges] using hC.1 heC
    exact heClique.card_eq
  have hePos : 0 < e.card := by omega
  obtain ⟨x, hxe⟩ := Finset.card_pos.mp hePos
  have hxQ := heQ hxe
  have hfaceX := G.erase_mem_triangles_of_isNClique_four hQ hxQ
  obtain ⟨f, hfC, hfFaceX⟩ := hC.2 hfaceX
  have hfQ : f ⊆ Q := hfFaceX.trans (Finset.erase_subset x Q)
  have hfFilter : f ∈ C.filter fun a => a ⊆ Q :=
    Finset.mem_filter.mpr ⟨hfC, hfQ⟩
  have hef : e = f :=
    Finset.card_le_one_iff.mp hcardLe heFilter hfFilter
  have hxf : x ∈ f := by simpa [hef] using hxe
  exact (Finset.mem_erase.mp (hfFaceX hxf)).1 rfl

/-- Restricting a transversal to the remaining edges after deleting a
four-clique still covers every remaining triangle. -/
theorem restrict_transversal_to_deleteEdgesWithin
    (G : SimpleGraph V) {Q : Finset V} {C : Finset (Finset V)}
    (hC : G.IsTriangleTransversal C) :
    (G.deleteEdgesWithin Q).IsTriangleTransversal
      (C ∩ (G.deleteEdgesWithin Q).edges) := by
  classical
  constructor
  · exact Finset.inter_subset_right
  · intro t ht
    have htG := (G.mem_triangles_deleteEdgesWithin_iff.mp ht).1
    obtain ⟨e, heC, het⟩ := hC.2 htG
    have heCard : e.card = 2 := by
      have heClique : G.IsNClique 2 e := by simpa [edges] using hC.1 heC
      exact heClique.card_eq
    have heDeleted : e ∈ (G.deleteEdgesWithin Q).edges :=
      (G.deleteEdgesWithin Q).mem_edges_of_subset_triangle ht het heCard
    exact ⟨e, Finset.mem_inter.mpr ⟨heC, heDeleted⟩, het⟩

/-- Deleting the six internal edges of a triangle-isolated `K₄` lowers the
triangle transversal number by exactly two. -/
theorem triangleTransversalNumber_eq_deleteEdgesWithin_add_two
    (G : SimpleGraph V) {Q : Finset V}
    (hQ : G.IsTriangleIsolatedK4 Q) :
    G.triangleTransversalNumber =
      (G.deleteEdgesWithin Q).triangleTransversalNumber + 2 := by
  classical
  apply le_antisymm
  · obtain ⟨C, hC, hCcard⟩ :=
      (G.deleteEdgesWithin Q).exists_min_triangleTransversal
    obtain ⟨H, hHedges, hHcard, hHcover⟩ :=
      G.exists_two_edge_cover_of_four_clique hQ.1
    have hUnion : G.IsTriangleTransversal (C ∪ H) := by
      constructor
      · intro e he
        rcases Finset.mem_union.mp he with heC | heH
        · exact G.edges_deleteEdgesWithin_subset (hC.1 heC)
        · exact hHedges heH
      · intro t ht
        by_cases htDeleted : t ∈ (G.deleteEdgesWithin Q).triangles
        · obtain ⟨e, heC, het⟩ := hC.2 htDeleted
          exact ⟨e, Finset.mem_union_left H heC, het⟩
        · have htQ :=
            G.subset_of_mem_triangles_not_mem_deleteEdgesWithin hQ ht htDeleted
          obtain ⟨e, heH, het⟩ :=
            hHcover htQ (G.card_eq_three_of_mem_triangles ht)
          exact ⟨e, Finset.mem_union_right C heH, het⟩
    have hτ := G.triangleTransversalNumber_le_card hUnion
    have hUnionCard := Finset.card_union_le C H
    omega
  · obtain ⟨C, hC, hCcard⟩ := G.exists_min_triangleTransversal
    let C' := C ∩ (G.deleteEdgesWithin Q).edges
    let D := C.filter fun e => e ⊆ Q
    have hC' : (G.deleteEdgesWithin Q).IsTriangleTransversal C' := by
      simpa [C'] using G.restrict_transversal_to_deleteEdgesWithin
        (Q := Q) hC
    have hDcard : 2 ≤ D.card := by
      simpa [D] using G.two_le_card_filter_subset_of_four_clique hQ.1 hC
    have hdisjoint : Disjoint C' D := by
      rw [Finset.disjoint_left]
      intro e heC' heD
      have heDeleted := (Finset.mem_inter.mp heC').2
      have heSub := (Finset.mem_filter.mp heD).2
      have heClique : (G.deleteEdgesWithin Q).IsNClique 2 e := by
        simpa [edges] using heDeleted
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp heClique.card_eq
      have huQ : u ∈ Q := heSub (by simp)
      have hvQ : v ∈ Q := heSub (by simp)
      have hadj := heClique.isClique (by simp) (by simp) huv
      exact hadj.2 ⟨huQ, hvQ⟩
    have hunionSub : C' ∪ D ⊆ C := by
      intro e he
      rcases Finset.mem_union.mp he with heC' | heD
      · exact (Finset.mem_inter.mp heC').1
      · exact (Finset.mem_filter.mp heD).1
    have hunionCard := Finset.card_le_card hunionSub
    have hcardEq := Finset.card_union_of_disjoint hdisjoint
    have hτ' := (G.deleteEdgesWithin Q).triangleTransversalNumber_le_card hC'
    omega

end SimpleGraph
