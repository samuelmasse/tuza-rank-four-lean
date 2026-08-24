import Mathlib.Tactic
import TuzaRankFour.Parker

/-!
# Fat-head crowns

This file fixes the exact crown object used in the rank-four reduction and
defines the graph left after deleting its crown vertices and head edges.
The complement of `crownVertices` is the set called `X` in the paper.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex spans an edge when together they form a graph triangle. -/
def Spans (G : SimpleGraph V) (c : V) (e : Finset V) : Prop :=
  e.card = 2 ∧ insert c e ∈ G.triangles

/-- The exact fat-head crown used in the twelve-vertex reduction.  In
particular, the witness is an edge-disjoint packing with one crown vertex and
one head edge in each of its triangles. -/
structure FatHeadCrown (G : SimpleGraph V) where
  crownVertices : Finset V
  headEdges : Finset (Finset V)
  witnessPacking : Finset (Finset V)
  crown_independent :
    ∀ ⦃u⦄, u ∈ crownVertices → ∀ ⦃v⦄, v ∈ crownVertices →
      u ≠ v → ¬G.Adj u v
  head_iff_spanned :
    ∀ e : Finset V, e ∈ headEdges ↔ ∃ c ∈ crownVertices, G.Spans c e
  separated :
    ∀ ⦃c⦄, c ∈ crownVertices → ∀ ⦃x⦄, x ∉ crownVertices →
      x ∉ headEdges.biUnion id → ¬G.Adj c x
  witness_isPacking : G.IsTrianglePacking witnessPacking
  witness_card : witnessPacking.card = headEdges.card
  witness_one_crown_vertex :
    ∀ ⦃t⦄, t ∈ witnessPacking → (t ∩ crownVertices).card = 1
  witness_one_head_edge :
    ∀ ⦃t⦄, t ∈ witnessPacking →
      (headEdges.filter fun e ↦ e ⊆ t).card = 1

namespace FatHeadCrown

variable {G : SimpleGraph V} (K : G.FatHeadCrown)

/-- Every head is a two-element graph edge. -/
theorem head_mem_edges {e : Finset V} (he : e ∈ K.headEdges) :
    e ∈ G.edges := by
  classical
  obtain ⟨c, hc, heCard, htriangle⟩ := (K.head_iff_spanned e).mp he
  exact G.mem_edges_of_subset_triangle htriangle (by simp) heCard

/-- A head edge has no endpoint in the crown. -/
theorem head_disjoint_crown {e : Finset V} (he : e ∈ K.headEdges) :
    Disjoint e K.crownVertices := by
  classical
  obtain ⟨c, hc, heCard, htriangle⟩ := (K.head_iff_spanned e).mp he
  have hcNot : c ∉ e := by
    intro hce
    have hcard := G.card_eq_three_of_mem_triangles htriangle
    simp [Finset.insert_eq_of_mem hce, heCard] at hcard
  have hclique : G.IsNClique 3 (insert c e) := by
    simpa [triangles] using htriangle
  rw [Finset.disjoint_left]
  intro x hxe hxC
  have hcx : c ≠ x := by
    intro h
    subst x
    exact hcNot hxe
  have hadj : G.Adj c x :=
    hclique.isClique (by simp) (by simp [hxe]) hcx
  exact K.crown_independent hc hxC hcx hadj

/-- Delete the crown vertices and all head edges, keeping the original vertex
type so that packing and transversal families can be compared directly. -/
def residual : SimpleGraph V where
  Adj u v :=
    G.Adj u v ∧ u ∉ K.crownVertices ∧ v ∉ K.crownVertices ∧
      ({u, v} : Finset V) ∉ K.headEdges
  symm.symm := by
    intro u v huv
    refine ⟨G.symm.symm u v huv.1, huv.2.2.1, huv.2.1, ?_⟩
    simpa [Finset.pair_comm] using huv.2.2.2
  loopless.irrefl := by
    intro u huu
    exact G.loopless.irrefl u huu.1

@[simp]
theorem residual_adj_iff {u v : V} :
    K.residual.Adj u v ↔
      G.Adj u v ∧ u ∉ K.crownVertices ∧ v ∉ K.crownVertices ∧
        ({u, v} : Finset V) ∉ K.headEdges :=
  Iff.rfl

/-- A residual edge is an edge of the original graph. -/
theorem residual_edges_subset : K.residual.edges ⊆ G.edges := by
  classical
  intro e he
  have heResidual : K.residual.IsNClique 2 e := by
    simpa [edges] using he
  have heG : G.IsNClique 2 e := by
    refine ⟨?_, heResidual.card_eq⟩
    intro u hu v hv huv
    exact (heResidual.isClique hu hv huv).1
  simpa [edges] using heG

/-- No residual edge is a head edge. -/
theorem residual_edge_not_head {e : Finset V}
    (he : e ∈ K.residual.edges) : e ∉ K.headEdges := by
  classical
  have heResidual : K.residual.IsNClique 2 e := by
    simpa [edges] using he
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp heResidual.card_eq
  exact (heResidual.isClique (by simp) (by simp) huv).2.2.2

/-- A residual edge has neither endpoint in the crown. -/
theorem residual_edge_disjoint_crown {e : Finset V}
    (he : e ∈ K.residual.edges) : Disjoint e K.crownVertices := by
  classical
  have heResidual : K.residual.IsNClique 2 e := by
    simpa [edges] using he
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp heResidual.card_eq
  rw [Finset.disjoint_left]
  intro x hx hxc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (heResidual.isClique (by simp) (by simp) huv).2.1 hxc
  · exact (heResidual.isClique (by simp) (by simp) huv).2.2.1 hxc

/-- Characterization of the triangles that survive crown deletion. -/
theorem mem_residual_triangles_iff {t : Finset V} :
    t ∈ K.residual.triangles ↔
      t ∈ G.triangles ∧ Disjoint t K.crownVertices ∧
        ∀ ⦃e⦄, e ∈ K.headEdges → ¬e ⊆ t := by
  classical
  constructor
  · intro ht
    have htResidual : K.residual.IsNClique 3 t := by
      simpa [triangles] using ht
    have htG : G.IsNClique 3 t := by
      refine ⟨?_, htResidual.card_eq⟩
      intro u hu v hv huv
      exact (htResidual.isClique hu hv huv).1
    refine ⟨by simpa [triangles] using htG, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro c hct hcC
      have hother : ∃ x ∈ t, x ≠ c := by
        by_contra h
        push Not at h
        have hsub : t ⊆ {c} := by
          intro x hx
          simp [h x hx]
        have := Finset.card_le_card hsub
        simp [htResidual.card_eq] at this
      obtain ⟨x, hxt, hxc⟩ := hother
      exact (htResidual.isClique hct hxt hxc.symm).2.1 hcC
    · intro e heH het
      have heCard : e.card = 2 := by
        obtain ⟨c, hc, hcard, htriangle⟩ := (K.head_iff_spanned e).mp heH
        exact hcard
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp heCard
      have hu : u ∈ t := het (by simp)
      have hv : v ∈ t := het (by simp)
      exact (htResidual.isClique hu hv huv).2.2.2 heH
  · rintro ⟨ht, htC, htH⟩
    have htG : G.IsNClique 3 t := by
      simpa [triangles] using ht
    have htResidual : K.residual.IsNClique 3 t := by
      refine ⟨?_, htG.card_eq⟩
      intro u hu v hv huv
      refine ⟨htG.isClique hu hv huv, ?_, ?_, ?_⟩
      · exact fun huC ↦ (Finset.disjoint_left.mp htC) hu huC
      · exact fun hvC ↦ (Finset.disjoint_left.mp htC) hv hvC
      · intro huvH
        exact htH huvH (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hu
          · exact hv)
    simpa [triangles] using htResidual

/-- Every original triangle deleted by the crown contains a head edge. -/
theorem exists_head_subset_of_not_mem_residual
    {t : Finset V} (ht : t ∈ G.triangles)
    (htResidual : t ∉ K.residual.triangles) :
    ∃ e ∈ K.headEdges, e ⊆ t := by
  classical
  by_contra hhead
  push Not at hhead
  have htNotDisjoint : ¬Disjoint t K.crownVertices := by
    intro htC
    apply htResidual
    exact K.mem_residual_triangles_iff.mpr ⟨ht, htC, hhead⟩
  obtain ⟨c, hct, hcC⟩ := Finset.not_disjoint_iff.mp htNotDisjoint
  let e := t.erase c
  have heCard : e.card = 2 := by
    simp [e, Finset.card_erase_of_mem hct,
      G.card_eq_three_of_mem_triangles ht]
  have heTriangle : insert c e ∈ G.triangles := by
    change insert c (t.erase c) ∈ G.triangles
    rw [Finset.insert_erase hct]
    exact ht
  have heHead : e ∈ K.headEdges :=
    (K.head_iff_spanned e).mpr ⟨c, hcC, heCard, heTriangle⟩
  exact hhead e heHead (by simpa [e] using Finset.erase_subset c t)

/-- A residual triangle and a witness triangle cannot share a graph edge. -/
theorem card_inter_residual_witness_le_one
    {r w : Finset V} (hr : r ∈ K.residual.triangles)
    (hw : w ∈ K.witnessPacking) :
    (r ∩ w).card ≤ 1 := by
  classical
  by_contra hlarge
  obtain ⟨e, heSub, heCard⟩ :=
    Finset.exists_subset_card_eq (s := r ∩ w) (n := 2) (by omega)
  have heR : e ⊆ r := heSub.trans Finset.inter_subset_left
  have heW : e ⊆ w := heSub.trans Finset.inter_subset_right
  have heResidual : e ∈ K.residual.edges :=
    K.residual.mem_edges_of_subset_triangle hr heR heCard
  have heDisjoint : Disjoint e K.crownVertices :=
    K.residual_edge_disjoint_crown heResidual
  have heSubDiff : e ⊆ w \ K.crownVertices := by
    intro x hxe
    exact Finset.mem_sdiff.mpr
      ⟨heW hxe, fun hxC ↦ (Finset.disjoint_left.mp heDisjoint) hxe hxC⟩
  have hwTriangle := K.witness_isPacking.1 hw
  have hwDiffCard : (w \ K.crownVertices).card = 2 := by
    rw [Finset.card_sdiff]
    have hwCard := G.card_eq_three_of_mem_triangles hwTriangle
    have hwC := K.witness_one_crown_vertex hw
    have hwC' : (K.crownVertices ∩ w).card = 1 := by
      simpa [Finset.inter_comm] using hwC
    omega
  have heEq : e = w \ K.crownVertices :=
    Finset.eq_of_subset_of_card_le heSubDiff (by omega)
  have hheads : (K.headEdges.filter fun a ↦ a ⊆ w).Nonempty := by
    rw [← Finset.card_pos]
    simp [K.witness_one_head_edge hw]
  obtain ⟨f, hf⟩ := hheads
  have hfData := Finset.mem_filter.mp hf
  have hfCard : f.card = 2 := by
    obtain ⟨c, hc, hcard, htriangle⟩ :=
      (K.head_iff_spanned f).mp hfData.1
    exact hcard
  have hfDisjoint : Disjoint f K.crownVertices :=
    K.head_disjoint_crown hfData.1
  have hfSubDiff : f ⊆ w \ K.crownVertices := by
    intro x hxf
    exact Finset.mem_sdiff.mpr
      ⟨hfData.2 hxf,
        fun hxC ↦ (Finset.disjoint_left.mp hfDisjoint) hxf hxC⟩
  have hfEq : f = w \ K.crownVertices :=
    Finset.eq_of_subset_of_card_le hfSubDiff (by omega)
  have heHead : e ∈ K.headEdges := by
    simpa [heEq, hfEq] using hfData.1
  exact K.residual_edge_not_head heResidual heHead

/-- Deleting a fat-head crown lowers the triangle packing number by exactly
the number of head edges. -/
theorem trianglePackingNumber_eq_residual_add_card :
    G.trianglePackingNumber =
      K.residual.trianglePackingNumber + K.headEdges.card := by
  classical
  apply le_antisymm
  · obtain ⟨P, hP, hPcard⟩ := G.exists_max_trianglePacking
    let good := P.filter fun t ↦ t ∈ K.residual.triangles
    let bad := P.filter fun t ↦ t ∉ K.residual.triangles
    have hgoodPacking : K.residual.IsTrianglePacking good := by
      constructor
      · intro t ht
        exact (Finset.mem_filter.mp ht).2
      · intro q hq r hr hqr
        exact hP.2 (Finset.mem_filter.mp hq).1
          (Finset.mem_filter.mp hr).1 hqr
    have hgoodBound : good.card ≤ K.residual.trianglePackingNumber :=
      K.residual.card_le_trianglePackingNumber hgoodPacking
    let chosenHead (t : ↑bad) : Finset V :=
      Classical.choose (K.exists_head_subset_of_not_mem_residual
        (hP.1 (Finset.mem_filter.mp t.property).1)
        (Finset.mem_filter.mp t.property).2)
    have chosenHead_mem (t : ↑bad) : chosenHead t ∈ K.headEdges :=
      (Classical.choose_spec (K.exists_head_subset_of_not_mem_residual
        (hP.1 (Finset.mem_filter.mp t.property).1)
        (Finset.mem_filter.mp t.property).2)).1
    have chosenHead_subset (t : ↑bad) : chosenHead t ⊆ t :=
      (Classical.choose_spec (K.exists_head_subset_of_not_mem_residual
        (hP.1 (Finset.mem_filter.mp t.property).1)
        (Finset.mem_filter.mp t.property).2)).2
    let headMap : ↑bad → ↑K.headEdges := fun t ↦
      ⟨chosenHead t, chosenHead_mem t⟩
    have headMap_injective : Function.Injective headMap := by
      intro q r hqr
      apply Subtype.ext
      by_contra hne
      have hqP := (Finset.mem_filter.mp q.property).1
      have hrP := (Finset.mem_filter.mp r.property).1
      have hchosen : chosenHead q = chosenHead r :=
        congrArg Subtype.val hqr
      have hinterSub : chosenHead q ⊆ (q : Finset V) ∩ r := by
        intro x hx
        exact Finset.mem_inter.mpr
          ⟨chosenHead_subset q hx,
            chosenHead_subset r (hchosen ▸ hx)⟩
      have hheadCard : (chosenHead q).card = 2 := by
        obtain ⟨c, hc, hcard, htriangle⟩ :=
          (K.head_iff_spanned (chosenHead q)).mp (chosenHead_mem q)
        exact hcard
      have hinterLower := Finset.card_le_card hinterSub
      have hinterUpper := hP.2 hqP hrP (by simpa using hne)
      omega
    have hbadBound : bad.card ≤ K.headEdges.card := by
      simpa using Fintype.card_le_of_injective headMap headMap_injective
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := P) (fun t ↦ t ∈ K.residual.triangles)
    change good.card + bad.card = P.card at hsplit
    omega
  · obtain ⟨P, hP, hPcard⟩ :=
      K.residual.exists_max_trianglePacking
    have hPG : G.IsTrianglePacking P := by
      constructor
      · intro t ht
        exact (K.mem_residual_triangles_iff.mp (hP.1 ht)).1
      · exact hP.2
    have hdisjoint : Disjoint P K.witnessPacking := by
      rw [Finset.disjoint_left]
      intro t htP htW
      have htC := (K.mem_residual_triangles_iff.mp (hP.1 htP)).2.1
      have htOne := K.witness_one_crown_vertex htW
      have : (t ∩ K.crownVertices).card = 0 := by
        rw [Finset.card_eq_zero,
          Finset.disjoint_iff_inter_eq_empty.mp htC]
      omega
    have hunion : G.IsTrianglePacking (P ∪ K.witnessPacking) := by
      constructor
      · intro t ht
        rcases Finset.mem_union.mp ht with htP | htW
        · exact hPG.1 htP
        · exact K.witness_isPacking.1 htW
      · intro q hq r hr hqr
        rcases Finset.mem_union.mp hq with hqP | hqW <;>
          rcases Finset.mem_union.mp hr with hrP | hrW
        · exact hPG.2 hqP hrP hqr
        · exact K.card_inter_residual_witness_le_one (hP.1 hqP) hrW
        · simpa [Finset.inter_comm] using
            K.card_inter_residual_witness_le_one (hP.1 hrP) hqW
        · exact K.witness_isPacking.2 hqW hrW hqr
    have hbound := G.card_le_trianglePackingNumber hunion
    rw [Finset.card_union_of_disjoint hdisjoint, hPcard,
      K.witness_card] at hbound
    exact hbound

/-- Every edge used to cover a witness triangle is deleted by the crown. -/
theorem edge_of_witness_not_mem_residual
    {t e : Finset V} (ht : t ∈ K.witnessPacking)
    (heG : e ∈ G.edges) (het : e ⊆ t) :
    e ∉ K.residual.edges := by
  classical
  intro heResidual
  have heCard : e.card = 2 := by
    have heClique : G.IsNClique 2 e := by
      simpa [edges] using heG
    exact heClique.card_eq
  have heDisjoint : Disjoint e K.crownVertices :=
    K.residual_edge_disjoint_crown heResidual
  have heSubDiff : e ⊆ t \ K.crownVertices := by
    intro x hxe
    exact Finset.mem_sdiff.mpr
      ⟨het hxe, fun hxC ↦ (Finset.disjoint_left.mp heDisjoint) hxe hxC⟩
  have htTriangle := K.witness_isPacking.1 ht
  have htDiffCard : (t \ K.crownVertices).card = 2 := by
    rw [Finset.card_sdiff]
    have htCard := G.card_eq_three_of_mem_triangles htTriangle
    have htC := K.witness_one_crown_vertex ht
    have htC' : (K.crownVertices ∩ t).card = 1 := by
      simpa [Finset.inter_comm] using htC
    omega
  have heEq : e = t \ K.crownVertices :=
    Finset.eq_of_subset_of_card_le heSubDiff (by omega)
  have hheads : (K.headEdges.filter fun a ↦ a ⊆ t).Nonempty := by
    rw [← Finset.card_pos]
    simp [K.witness_one_head_edge ht]
  obtain ⟨f, hf⟩ := hheads
  have hfData := Finset.mem_filter.mp hf
  have hfCard : f.card = 2 := by
    obtain ⟨c, hc, hcard, htriangle⟩ :=
      (K.head_iff_spanned f).mp hfData.1
    exact hcard
  have hfDisjoint : Disjoint f K.crownVertices :=
    K.head_disjoint_crown hfData.1
  have hfSubDiff : f ⊆ t \ K.crownVertices := by
    intro x hxf
    exact Finset.mem_sdiff.mpr
      ⟨hfData.2 hxf,
        fun hxC ↦ (Finset.disjoint_left.mp hfDisjoint) hxf hxC⟩
  have hfEq : f = t \ K.crownVertices :=
    Finset.eq_of_subset_of_card_le hfSubDiff (by omega)
  have heHead : e ∈ K.headEdges := by
    simpa [heEq, hfEq] using hfData.1
  exact K.residual_edge_not_head heResidual heHead

/-- Deleting a fat-head crown lowers the triangle transversal number by
exactly the number of head edges. -/
theorem triangleTransversalNumber_eq_residual_add_card :
    G.triangleTransversalNumber =
      K.residual.triangleTransversalNumber + K.headEdges.card := by
  classical
  apply le_antisymm
  · obtain ⟨C, hC, hCcard⟩ :=
      K.residual.exists_min_triangleTransversal
    have hUnion : G.IsTriangleTransversal (C ∪ K.headEdges) := by
      constructor
      · intro e he
        rcases Finset.mem_union.mp he with heC | heH
        · exact K.residual_edges_subset (hC.1 heC)
        · exact K.head_mem_edges heH
      · intro t ht
        by_cases htResidual : t ∈ K.residual.triangles
        · obtain ⟨e, heC, het⟩ := hC.2 htResidual
          exact ⟨e, Finset.mem_union_left _ heC, het⟩
        · obtain ⟨e, heH, het⟩ :=
            K.exists_head_subset_of_not_mem_residual ht htResidual
          exact ⟨e, Finset.mem_union_right _ heH, het⟩
    calc
      G.triangleTransversalNumber ≤ (C ∪ K.headEdges).card :=
        G.triangleTransversalNumber_le_card hUnion
      _ ≤ C.card + K.headEdges.card := Finset.card_union_le C K.headEdges
      _ = K.residual.triangleTransversalNumber + K.headEdges.card := by
        rw [hCcard]
  · obtain ⟨C, hC, hCcard⟩ := G.exists_min_triangleTransversal
    let kept := C.filter fun e ↦ e ∈ K.residual.edges
    let removed := C.filter fun e ↦ e ∉ K.residual.edges
    have hkept : K.residual.IsTriangleTransversal kept := by
      constructor
      · intro e he
        exact (Finset.mem_filter.mp he).2
      · intro t ht
        have htG := (K.mem_residual_triangles_iff.mp ht).1
        obtain ⟨e, heC, het⟩ := hC.2 htG
        have heCard : e.card = 2 := by
          have heClique : G.IsNClique 2 e := by
            simpa [edges] using hC.1 heC
          exact heClique.card_eq
        have heResidual : e ∈ K.residual.edges :=
          K.residual.mem_edges_of_subset_triangle ht het heCard
        exact ⟨e, Finset.mem_filter.mpr ⟨heC, heResidual⟩, het⟩
    have hkeptBound :
        K.residual.triangleTransversalNumber ≤ kept.card :=
      K.residual.triangleTransversalNumber_le_card hkept
    let chosenEdge (t : ↑K.witnessPacking) : Finset V :=
      Classical.choose (hC.2 (K.witness_isPacking.1 t.property))
    have chosenEdge_mem_C (t : ↑K.witnessPacking) : chosenEdge t ∈ C :=
      (Classical.choose_spec
        (hC.2 (K.witness_isPacking.1 t.property))).1
    have chosenEdge_subset (t : ↑K.witnessPacking) : chosenEdge t ⊆ t :=
      (Classical.choose_spec
        (hC.2 (K.witness_isPacking.1 t.property))).2
    have chosenEdge_removed (t : ↑K.witnessPacking) :
        chosenEdge t ∈ removed := by
      refine Finset.mem_filter.mpr ⟨chosenEdge_mem_C t, ?_⟩
      exact K.edge_of_witness_not_mem_residual t.property
        (hC.1 (chosenEdge_mem_C t)) (chosenEdge_subset t)
    let edgeMap : ↑K.witnessPacking → ↑removed := fun t ↦
      ⟨chosenEdge t, chosenEdge_removed t⟩
    have edgeMap_injective : Function.Injective edgeMap := by
      intro q r hqr
      apply Subtype.ext
      by_contra hne
      have hchosen : chosenEdge q = chosenEdge r :=
        congrArg Subtype.val hqr
      have hinterSub : chosenEdge q ⊆ (q : Finset V) ∩ r := by
        intro x hx
        exact Finset.mem_inter.mpr
          ⟨chosenEdge_subset q hx,
            chosenEdge_subset r (hchosen ▸ hx)⟩
      have hchosenCard : (chosenEdge q).card = 2 := by
        have heClique : G.IsNClique 2 (chosenEdge q) := by
          simpa [edges] using hC.1 (chosenEdge_mem_C q)
        exact heClique.card_eq
      have hinterLower := Finset.card_le_card hinterSub
      have hinterUpper := K.witness_isPacking.2 q.property r.property
        (by simpa using hne)
      omega
    have hremovedBound : K.headEdges.card ≤ removed.card := by
      rw [← K.witness_card]
      simpa using Fintype.card_le_of_injective edgeMap edgeMap_injective
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := C) (fun e ↦ e ∈ K.residual.edges)
    change kept.card + removed.card = C.card at hsplit
    omega

end FatHeadCrown

end SimpleGraph
