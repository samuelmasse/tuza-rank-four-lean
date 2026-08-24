import TuzaRankFour.ComponentTransfer

/-!
# Internal residual vertices

This file proves the split-normal confinement statement needed for the final
discharge: a residual vertex in an all-excellent packing component has no
neighbour outside that component's packing support.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A packing component is all-excellent when every packed triangle in it is
excellent. -/
def IsAllExcellentPackingComponent (G : SimpleGraph V)
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) : Prop :=
  packingComponentTriangles S C ⊆ G.excellentPackingTriangles S

/-- An all-good component is a transfer component precisely when it contains
a pretty-good packed triangle. -/
def PackingComponentHasPrettyGood (G : SimpleGraph V)
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) : Prop :=
  ∃ t ∈ packingComponentTriangles S C,
    t ∈ G.prettyGoodPackingTriangles S

/-- An all-good component with no pretty-good member is all-excellent. -/
theorem isAllExcellent_of_isAllGood_of_not_hasPrettyGood
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllGood : G.IsAllGoodPackingComponent S C)
    (hNoPretty : ¬G.PackingComponentHasPrettyGood S C) :
    G.IsAllExcellentPackingComponent S C := by
  classical
  intro t htC
  have htGood := hAllGood htC
  have htPartition :
      t ∈ G.excellentPackingTriangles S ∨
        t ∈ G.prettyGoodPackingTriangles S := by
    have hEq := congrArg (fun Q : Finset (Finset V) ↦ t ∈ Q)
      (G.excellent_union_prettyGood_eq_good S)
    simpa only [Finset.mem_union] using hEq.mpr htGood
  exact htPartition.resolve_right (fun htPretty ↦
    hNoPretty ⟨t, htC, htPretty⟩)

/-- A component containing a pretty-good packed triangle contains a
pretty-good residual vertex in its own support. -/
theorem exists_prettyGoodResidualVertex_in_component
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hPretty : G.PackingComponentHasPrettyGood S C) :
    ∃ z,
      z ∈ packingComponentVertexSupport S C ∧
      z ∈ G.prettyGoodResidualVertices S := by
  classical
  obtain ⟨t, htC, htPretty⟩ := hPretty
  obtain ⟨z, hzt, hzResidual⟩ :=
    G.exists_prettyGoodResidualVertex_of_mem_prettyGoodPackingTriangles
      hS hNoK4 htPretty
  exact ⟨z, Finset.mem_biUnion.mpr ⟨t, htC, hzt⟩, hzResidual⟩

/-- Any packed triangle containing a vertex of a packing component belongs to
that component. -/
theorem mem_component_of_mem_componentSupport_of_mem_packingTriangle
    {S : Finset (Finset V)}
    {C : (packingIntersectionGraph S).ConnectedComponent}
    {z : V} (hzC : z ∈ packingComponentVertexSupport S C)
    {t : Finset V} (htS : t ∈ S) (hzt : z ∈ t) :
    t ∈ packingComponentTriangles S C := by
  classical
  obtain ⟨s, hsC, hzs⟩ := Finset.mem_biUnion.mp hzC
  by_cases hst : s = t
  · simpa [hst] using hsC
  · exact mem_packingComponentTriangles_of_inter_nonempty hsC htS hst
      ⟨z, Finset.mem_inter.mpr ⟨hzs, hzt⟩⟩

/-- An all-excellent component contains a residual vertex of the excellent
class. -/
theorem exists_excellentResidualVertex_in_allExcellent_component
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllExcellent : G.IsAllExcellentPackingComponent S C) :
    ∃ z,
      z ∈ packingComponentVertexSupport S C ∧
      z ∈ G.excellentResidualVertices S := by
  classical
  obtain ⟨q, hqC⟩ := C.nonempty_supp
  let t : Finset V := q.1
  have htS : t ∈ S := q.2
  have htC : t ∈ packingComponentTriangles S C := by
    rw [mem_packingComponentTriangles_iff]
    exact ⟨⟨q, hqC⟩, rfl⟩
  have htExcellent :=
    G.mem_excellentPackingTriangles_iff.mp (hAllExcellent htC)
  obtain ⟨e, heSlice⟩ :=
    (G.mem_goodPackingTriangles_iff.mp htExcellent.1).2
  have heData := Finset.mem_inter.mp heSlice
  have htCard : t.card = 3 :=
    G.card_eq_three_of_mem_triangles (hS.1.1 htS)
  obtain ⟨z, hzNotE, htInsert⟩ :=
    exists_complement_vertex_of_powersetCard_two htCard heData.1
  have hzt : z ∈ t := by rw [htInsert]; simp
  have hzNotLabelled := G.opposite_vertex_not_mem_labelledPackingVertices
    hS hNoK4 htS heSlice hzt hzNotE
  have hzNotPrettySupport :
      z ∉ triangleFamilyVertexSupport (G.prettyGoodPackingTriangles S) := by
    intro hzPrettySupport
    obtain ⟨p, hpPretty, hzp⟩ := Finset.mem_biUnion.mp hzPrettySupport
    have hpS := (G.mem_goodPackingTriangles_iff.mp
      (G.mem_prettyGoodPackingTriangles_iff.mp hpPretty).1).1
    have hpC :=
      mem_component_of_mem_componentSupport_of_mem_packingTriangle
        (Finset.mem_biUnion.mpr ⟨t, htC, hzt⟩) hpS hzp
    have hpExcellent := hAllExcellent hpC
    exact Finset.disjoint_left.mp (G.disjoint_excellent_prettyGood S)
      hpExcellent hpPretty
  have hzNotBadSupport :
      z ∉ triangleFamilyVertexSupport (G.badPackingTriangles S) := by
    intro hzBadSupport
    obtain ⟨p, hpBad, hzp⟩ := Finset.mem_biUnion.mp hzBadSupport
    have hpS := (G.mem_badPackingTriangles_iff.mp hpBad).1
    have hpC :=
      mem_component_of_mem_componentSupport_of_mem_packingTriangle
        (Finset.mem_biUnion.mpr ⟨t, htC, hzt⟩) hpS hzp
    have hpExcellentData :=
      G.mem_excellentPackingTriangles_iff.mp (hAllExcellent hpC)
    have hpGood := hpExcellentData.1
    exact Finset.disjoint_left.mp (G.disjoint_good_bad S) hpGood hpBad
  refine ⟨z, Finset.mem_biUnion.mpr ⟨t, htC, hzt⟩, ?_⟩
  rw [G.mem_excellentResidualVertices_iff]
  exact ⟨Finset.mem_biUnion.mpr
      ⟨t, G.mem_excellentPackingTriangles_iff.mpr htExcellent, hzt⟩,
    hzNotLabelled, hzNotPrettySupport, hzNotBadSupport⟩

/-- Three distinct, pairwise adjacent vertices form a graph triangle. -/
theorem mem_triangles_of_three_pairwise_adj
    (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ({a, b, c} : Finset V) ∈ G.triangles := by
  classical
  have habNe : a ≠ b := G.ne_of_adj hab
  have hacNe : a ≠ c := G.ne_of_adj hac
  have hbcNe : b ≠ c := G.ne_of_adj hbc
  have hclique : G.IsClique ((({a, b, c} : Finset V) : Set V)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact hab
    · exact hac
    · exact G.symm.symm _ _ hab
    · exact (hxy rfl).elim
    · exact hbc
    · exact G.symm.symm _ _ hac
    · exact G.symm.symm _ _ hbc
    · exact (hxy rfl).elim
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    simp [habNe, hacNe, hbcNe]
  simpa [triangles] using (show G.IsNClique 3 ({a, b, c} : Finset V) from
    ⟨hclique, hcard⟩)

/-- A labelled packing edge cannot contain a vertex outside the labelled
packing vertex set. -/
theorem not_mem_labelledPackingEdges_of_endpoint_not_labelled
    (G : SimpleGraph V) {S : Finset (Finset V)}
    {z : V} (hz : z ∉ G.labelledPackingVertices S)
    {e : Finset V} (hze : z ∈ e) :
    e ∉ G.labelledPackingEdges S := by
  intro he
  exact hz (G.mem_labelledPackingVertices_iff.mpr ⟨e, he, hze⟩)

/-- If a vertex spans an unlabelled edge and is not incident with any labelled
edge, the resulting triangle survives deletion of all labelled edges. -/
theorem triangleAvoidsPackingLabels_of_spans_unlabelled
    (G : SimpleGraph V) {S : Finset (Finset V)}
    {z : V} (hz : z ∉ G.labelledPackingVertices S)
    {e : Finset V} (hze : G.Spans z e)
    (heUnlabelled : e ∉ G.labelledPackingEdges S) :
    G.TriangleAvoidsPackingLabels S (insert z e) := by
  classical
  refine ⟨hze.2, ?_⟩
  rw [Finset.disjoint_left]
  intro f hfTriangle hfLabelled
  have hfData := Finset.mem_powersetCard.mp hfTriangle
  by_cases hzf : z ∈ f
  · exact G.not_mem_labelledPackingEdges_of_endpoint_not_labelled
      hz hzf hfLabelled
  · have hfSubE : f ⊆ e := by
      intro a haf
      have haInsert := hfData.1 haf
      rcases Finset.mem_insert.mp haInsert with haz | hae
      · exact (hzf (haz ▸ haf)).elim
      · exact hae
    have hfEq : f = e :=
      Finset.eq_of_subset_of_card_le hfSubE (by
        have hfCard := hfData.2
        have heCard := hze.1
        omega)
    exact heUnlabelled (hfEq ▸ hfLabelled)

/-- No triangle in the link of an internal residual vertex can cross the
boundary of an all-excellent packing component. -/
theorem false_of_residual_link_crosses_allExcellent_component
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllExcellent : G.IsAllExcellentPackingComponent S C)
    {z a b : V}
    (hzC : z ∈ packingComponentVertexSupport S C)
    (haC : a ∈ packingComponentVertexSupport S C)
    (hbOutside : b ∉ packingComponentVertexSupport S C)
    (hzNotLabelled : z ∉ G.labelledPackingVertices S)
    (hza : G.Adj z a) (hzb : G.Adj z b) (hab : G.Adj a b) :
    False := by
  classical
  have hr : ({z, a, b} : Finset V) ∈ G.triangles :=
    G.mem_triangles_of_three_pairwise_adj hza hzb hab
  obtain ⟨p, hpS, hinter⟩ :=
    G.exists_two_le_card_inter_of_isSupportMaximalPacking hS hr
  obtain ⟨f, hfSub, hfCard⟩ :=
    Finset.exists_subset_card_eq (s := p ∩ ({z, a, b} : Finset V))
      (n := 2) hinter
  have hfP : f ∈ p.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_left, hfCard⟩
  have hfR : f ∈ ({z, a, b} : Finset V).powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_right, hfCard⟩
  have hzaNe : z ≠ a := G.ne_of_adj hza
  have hzbNe : z ≠ b := G.ne_of_adj hzb
  have habNe : a ≠ b := G.ne_of_adj hab
  have hfEqZa : f = ({z, a} : Finset V) := by
    rcases (mem_powersetCard_two_triple_iff
        hzaNe hzbNe habNe).mp hfR with hfEq | hfEq | hfEq
    · exact hfEq
    · have hzp : z ∈ p :=
        (Finset.mem_powersetCard.mp hfP).1 (hfEq ▸ (by simp))
      have hpC :=
        mem_component_of_mem_componentSupport_of_mem_packingTriangle
          hzC hpS hzp
      have hbp : b ∈ p :=
        (Finset.mem_powersetCard.mp hfP).1 (hfEq ▸ (by simp))
      exact (hbOutside (Finset.mem_biUnion.mpr ⟨p, hpC, hbp⟩)).elim
    · have hap : a ∈ p :=
        (Finset.mem_powersetCard.mp hfP).1 (hfEq ▸ (by simp))
      have hpC :=
        mem_component_of_mem_componentSupport_of_mem_packingTriangle
          haC hpS hap
      have hbp : b ∈ p :=
        (Finset.mem_powersetCard.mp hfP).1 (hfEq ▸ (by simp))
      exact (hbOutside (Finset.mem_biUnion.mpr ⟨p, hpC, hbp⟩)).elim
  have hzp : z ∈ p :=
    (Finset.mem_powersetCard.mp hfP).1 (hfEqZa ▸ (by simp))
  have hpC :=
    mem_component_of_mem_componentSupport_of_mem_packingTriangle
      hzC hpS hzp
  have hpExcellent :=
    G.mem_excellentPackingTriangles_iff.mp (hAllExcellent hpC)
  have hzaUnlabelled : ({z, a} : Finset V) ∉
      G.labelledPackingEdges S :=
    G.not_mem_labelledPackingEdges_of_endpoint_not_labelled
      hzNotLabelled (by simp)
  have hzbNotFamily : ({z, b} : Finset V) ∉ triangleFamilyEdges S := by
    intro hFamily
    obtain ⟨q, hqS, hzbSub, _⟩ := mem_triangleFamilyEdges_iff.mp hFamily
    have hzq : z ∈ q := hzbSub (by simp)
    have hqC :=
      mem_component_of_mem_componentSupport_of_mem_packingTriangle
        hzC hqS hzq
    exact hbOutside (Finset.mem_biUnion.mpr ⟨q, hqC, hzbSub (by simp)⟩)
  have habNotFamily : ({a, b} : Finset V) ∉ triangleFamilyEdges S := by
    intro hFamily
    obtain ⟨q, hqS, habSub, _⟩ := mem_triangleFamilyEdges_iff.mp hFamily
    have haq : a ∈ q := habSub (by simp)
    have hqC :=
      mem_component_of_mem_componentSupport_of_mem_packingTriangle
        haC hqS haq
    exact hbOutside (Finset.mem_biUnion.mpr ⟨q, hqC, habSub (by simp)⟩)
  have hzbUnlabelled : ({z, b} : Finset V) ∉
      G.labelledPackingEdges S := fun h ↦
    hzbNotFamily (G.mem_labelledPackingEdges_iff.mp h).1
  have habUnlabelled : ({a, b} : Finset V) ∉
      G.labelledPackingEdges S := fun h ↦
    habNotFamily (G.mem_labelledPackingEdges_iff.mp h).1
  have hrAvoids : G.TriangleAvoidsPackingLabels S {z, a, b} := by
    refine ⟨hr, ?_⟩
    rw [Finset.disjoint_left]
    intro e heR heLabelled
    rcases (mem_powersetCard_two_triple_iff
        hzaNe hzbNe habNe).mp heR with hEq | hEq | hEq
    · exact hzaUnlabelled (hEq ▸ heLabelled)
    · exact hzbUnlabelled (hEq ▸ heLabelled)
    · exact habUnlabelled (hEq ▸ heLabelled)
  exact hpExcellent.2
    (hfEqZa ▸ hfP) hzaUnlabelled hrAvoids (by simp)

/-- Every neighbour of an internal residual vertex in an all-excellent
component remains in that component's packing support. -/
theorem neighbor_mem_componentSupport_of_allExcellent
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hSplit : G.IsSplitNormal)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllExcellent : G.IsAllExcellentPackingComponent S C)
    {z : V} (hzC : z ∈ packingComponentVertexSupport S C)
    (hzNotLabelled : z ∉ G.labelledPackingVertices S)
    {b : V} (hzb : G.Adj z b) :
    b ∈ packingComponentVertexSupport S C := by
  classical
  obtain ⟨t, htC, hzt⟩ := Finset.mem_biUnion.mp hzC
  have hzt' : z ∈ t := by simpa using hzt
  have htS := packingComponentTriangles_subset C htC
  have htTriangle := hS.1.1 htS
  have htCard : t.card = 3 := G.card_eq_three_of_mem_triangles htTriangle
  have hEraseCard : (t.erase z).card = 2 := by
    rw [Finset.card_erase_of_mem hzt', htCard]
  obtain ⟨a, haErase⟩ := Finset.card_pos.mp (by omega : 0 < (t.erase z).card)
  have hat : a ∈ t := Finset.mem_of_mem_erase haErase
  have haz : a ≠ z := (Finset.mem_erase.mp haErase).1
  have htClique : G.IsNClique 3 t := by simpa [triangles] using htTriangle
  have hza : G.Adj z a :=
    htClique.isClique hzt' hat (fun h ↦ haz h.symm)
  have haC : a ∈ packingComponentVertexSupport S C :=
    Finset.mem_biUnion.mpr ⟨t, htC, hat⟩
  let a' : G.neighborSet z := ⟨a, hza⟩
  let b' : G.neighborSet z := ⟨b, hzb⟩
  have hReach : (G.triangleLink z).Reachable b' a' :=
    (hSplit z a' b').symm
  rw [reachable_iff_reflTransGen] at hReach
  exact Relation.ReflTransGen.head_induction_on
    (motive := fun c _ ↦ c.1 ∈ packingComponentVertexSupport S C)
    hReach haC (by
      intro c d hcd _ hdC
      by_contra hcOutside
      exact G.false_of_residual_link_crosses_allExcellent_component
        hS C hAllExcellent hzC hdC hcOutside hzNotLabelled
        d.2 c.2 (G.symm.symm _ _ ((G.triangleLink_adj_iff z).mp hcd)))

/-- Every edge spanned by an internal residual vertex of an all-excellent
component is a labelled packing edge. -/
theorem mem_labelledPackingEdges_of_spans_allExcellent
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hSplit : G.IsSplitNormal)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllExcellent : G.IsAllExcellentPackingComponent S C)
    {z : V} (hzC : z ∈ packingComponentVertexSupport S C)
    (hzNotLabelled : z ∉ G.labelledPackingVertices S)
    {e : Finset V} (hze : G.Spans z e) :
    e ∈ G.labelledPackingEdges S := by
  classical
  by_contra heUnlabelled
  have heCard : e.card = 2 := hze.1
  obtain ⟨a, b, hab, heEq⟩ := Finset.card_eq_two.mp heCard
  have hrAvoids := G.triangleAvoidsPackingLabels_of_spans_unlabelled
    hzNotLabelled hze heUnlabelled
  have hrClique : G.IsNClique 3 (insert z e) := by
    simpa [triangles] using hze.2
  have hzNotE : z ∉ e := by
    intro hzE
    have hcard := G.card_eq_three_of_mem_triangles hze.2
    rw [Finset.insert_eq_of_mem hzE, heCard] at hcard
    omega
  have hzaNe : z ≠ a := fun h ↦ hzNotE (h ▸ (by simp [heEq]))
  have hzbNe : z ≠ b := fun h ↦ hzNotE (h ▸ (by simp [heEq]))
  have hza : G.Adj z a := by
    apply hrClique.isClique
    · simp
    · simp [heEq]
    · exact hzaNe
  have hzb : G.Adj z b := by
    apply hrClique.isClique
    · simp
    · simp [heEq]
    · exact hzbNe
  have haC := G.neighbor_mem_componentSupport_of_allExcellent
    hS hSplit C hAllExcellent hzC hzNotLabelled hza
  have hbC := G.neighbor_mem_componentSupport_of_allExcellent
    hS hSplit C hAllExcellent hzC hzNotLabelled hzb
  obtain ⟨p, hpS, hinter⟩ :=
    G.exists_two_le_card_inter_of_isSupportMaximalPacking hS hze.2
  obtain ⟨f, hfSub, hfCard⟩ :=
    Finset.exists_subset_card_eq (s := p ∩ insert z e) (n := 2) hinter
  have hfP : f ∈ p.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_left, hfCard⟩
  have hfR : f ∈ (insert z e).powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_right, hfCard⟩
  have hfCases :
      f = ({z, a} : Finset V) ∨ f = {z, b} ∨ f = {a, b} := by
    rw [heEq] at hfR
    exact (mem_powersetCard_two_triple_iff hzaNe hzbNe hab).mp hfR
  have hpC : p ∈ packingComponentTriangles S C := by
    rcases hfCases with hfEq | hfEq | hfEq
    · have hzp : z ∈ p :=
        (Finset.mem_powersetCard.mp hfP).1 (hfEq ▸ (by simp))
      exact mem_component_of_mem_componentSupport_of_mem_packingTriangle
        hzC hpS hzp
    · have hzp : z ∈ p :=
        (Finset.mem_powersetCard.mp hfP).1 (hfEq ▸ (by simp))
      exact mem_component_of_mem_componentSupport_of_mem_packingTriangle
        hzC hpS hzp
    · have hap : a ∈ p :=
        (Finset.mem_powersetCard.mp hfP).1 (hfEq ▸ (by simp))
      exact mem_component_of_mem_componentSupport_of_mem_packingTriangle
        haC hpS hap
  have hpExcellent :=
    G.mem_excellentPackingTriangles_iff.mp (hAllExcellent hpC)
  have hfUnlabelled : f ∉ G.labelledPackingEdges S :=
    Finset.disjoint_left.mp hrAvoids.2 hfR
  exact hpExcellent.2 hfP hfUnlabelled hrAvoids
    (Finset.mem_powersetCard.mp hfR).1

/-- An internal residual vertex in an all-excellent component spans only
labelled edges that retain their unit in the transfer ledger. -/
theorem LabelledTransferLedger.mem_remainingEdges_of_spans_internal
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (D : G.LabelledTransferLedger S)
    (hS : G.IsSupportMaximalPacking S)
    (hSplit : G.IsSplitNormal)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllExcellent : G.IsAllExcellentPackingComponent S C)
    {z : V} (hzC : z ∈ packingComponentVertexSupport S C)
    (hzNotLabelled : z ∉ G.labelledPackingVertices S)
    {e : Finset V} (hze : G.Spans z e) :
    e ∈ D.remainingEdges := by
  classical
  have heLabelled := G.mem_labelledPackingEdges_of_spans_allExcellent
    hS hSplit C hAllExcellent hzC hzNotLabelled hze
  rw [D.mem_remainingEdges_iff]
  refine ⟨heLabelled, ?_⟩
  intro heDepleted
  obtain ⟨p, hpS, heSubP, heCard⟩ :=
    mem_triangleFamilyEdges_iff.mp
      (G.mem_labelledPackingEdges_iff.mp heLabelled).1
  have heP : e ∈ p.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨heSubP, heCard⟩
  obtain ⟨a, hae⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
  have hrClique : G.IsNClique 3 (insert z e) := by
    simpa [triangles] using hze.2
  have hza : G.Adj z a := by
    apply hrClique.isClique
    · simp
    · exact Finset.mem_insert_of_mem hae
    · intro h
      subst z
      have hcard := G.card_eq_three_of_mem_triangles hze.2
      simp [Finset.insert_eq_of_mem hae, heCard] at hcard
  have haC := G.neighbor_mem_componentSupport_of_allExcellent
    hS hSplit C hAllExcellent hzC hzNotLabelled hza
  have hap : a ∈ p := heSubP hae
  have hpC :=
    mem_component_of_mem_componentSupport_of_mem_packingTriangle
      haC hpS hap
  have hpExcellent := hAllExcellent hpC
  obtain ⟨t, htPretty, heSubT⟩ := D.depleted_owned_by_prettyGood heDepleted
  have htS := (G.mem_goodPackingTriangles_iff.mp
    (G.mem_prettyGoodPackingTriangles_iff.mp htPretty).1).1
  have heT : e ∈ t.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨heSubT, heCard⟩
  have hpt := G.eq_of_mem_powersetCard_of_isTrianglePacking
    hS.1 hpS htS heP heT
  have hpPretty : p ∈ G.prettyGoodPackingTriangles S := hpt ▸ htPretty
  exact Finset.disjoint_left.mp (G.disjoint_excellent_prettyGood S)
    hpExcellent hpPretty

end SimpleGraph
