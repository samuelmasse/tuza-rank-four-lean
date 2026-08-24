import TuzaRankFour.InternalResidual

/-!
# Global discharge assembly

This file assembles the packing-component count, the canonical residual
representatives, and the transfer ledger used by the final crown argument.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The packed triangles are the disjoint union of their intersection-graph
components. -/
theorem biUnion_packingComponentTriangles
    (S : Finset (Finset V)) :
    Finset.univ.biUnion (packingComponentTriangles S) = S := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨C, _, htC⟩ := Finset.mem_biUnion.mp ht
    exact packingComponentTriangles_subset C htC
  · intro htS
    let q : {p : Finset V // p ∈ S} := ⟨t, htS⟩
    let C := (packingIntersectionGraph S).connectedComponentMk q
    have hqC : q ∈ C.supp := (C.mem_supp_iff q).mpr rfl
    have htC : t ∈ packingComponentTriangles S C :=
      mem_packingComponentTriangles_iff.mpr ⟨⟨q, hqC⟩, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, htC⟩

/-- Triangle families belonging to distinct packing components are disjoint. -/
theorem pairwiseDisjoint_packingComponentTriangles
    (S : Finset (Finset V)) :
    (Set.univ : Set
      (packingIntersectionGraph S).ConnectedComponent).PairwiseDisjoint
        (packingComponentTriangles S) := by
  classical
  intro C _ D _ hCD
  change Disjoint (packingComponentTriangles S C)
    (packingComponentTriangles S D)
  rw [Finset.disjoint_left]
  intro t htC htD
  obtain ⟨q, hqEq⟩ := mem_packingComponentTriangles_iff.mp htC
  obtain ⟨r, hrEq⟩ := mem_packingComponentTriangles_iff.mp htD
  have hqr : q.1 = r.1 := Subtype.ext (hqEq.trans hrEq.symm)
  have hqC :
      (packingIntersectionGraph S).connectedComponentMk q.1 = C :=
    (C.mem_supp_iff q.1).mp q.2
  have hrD :
      (packingIntersectionGraph S).connectedComponentMk r.1 = D :=
    (D.mem_supp_iff r.1).mp r.2
  apply hCD
  calc
    C = (packingIntersectionGraph S).connectedComponentMk q.1 := hqC.symm
    _ = (packingIntersectionGraph S).connectedComponentMk r.1 := congrArg _ hqr
    _ = D := hrD

/-- The component triangle cardinalities sum to the packing cardinality. -/
theorem sum_card_packingComponentTriangles
    (S : Finset (Finset V)) :
    ∑ C : (packingIntersectionGraph S).ConnectedComponent,
        (packingComponentTriangles S C).card = S.card := by
  classical
  have hcard := congrArg Finset.card (biUnion_packingComponentTriangles S)
  rw [Finset.card_biUnion (by
    simpa using pairwiseDisjoint_packingComponentTriangles S)] at hcard
  simpa using hcard

/-- The packing support is the disjoint union of the vertex supports of its
intersection components. -/
theorem biUnion_packingComponentVertexSupport
    (S : Finset (Finset V)) :
    Finset.univ.biUnion (packingComponentVertexSupport S) =
      triangleFamilyVertexSupport S := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨C, _, hzC⟩ := Finset.mem_biUnion.mp hz
    exact packingComponentVertexSupport_subset C hzC
  · intro hz
    obtain ⟨t, htS, hzt⟩ := Finset.mem_biUnion.mp hz
    let q : {p : Finset V // p ∈ S} := ⟨t, htS⟩
    let C := (packingIntersectionGraph S).connectedComponentMk q
    have hqC : q ∈ C.supp := (C.mem_supp_iff q).mpr rfl
    have htC : t ∈ packingComponentTriangles S C :=
      mem_packingComponentTriangles_iff.mpr ⟨⟨q, hqC⟩, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨C, Finset.mem_univ C, Finset.mem_biUnion.mpr ⟨t, htC, hzt⟩⟩

/-- The support cardinality is the sum of the component support
cardinalities. -/
theorem card_triangleFamilyVertexSupport_eq_sum_components
    (S : Finset (Finset V)) :
    (triangleFamilyVertexSupport S).card =
      ∑ C : (packingIntersectionGraph S).ConnectedComponent,
        (packingComponentVertexSupport S C).card := by
  classical
  have hpair :
      (Set.univ : Set
        (packingIntersectionGraph S).ConnectedComponent).PairwiseDisjoint
          (packingComponentVertexSupport S) := by
    intro C _ D _ hCD
    exact disjoint_packingComponentVertexSupport hCD
  have hcard := congrArg Finset.card
    (biUnion_packingComponentVertexSupport S)
  rw [Finset.card_biUnion (by simpa using hpair)] at hcard
  exact hcard.symm

/-- The all-good packing components. -/
noncomputable def allGoodPackingComponents (G : SimpleGraph V)
    (S : Finset (Finset V)) :
    Finset (packingIntersectionGraph S).ConnectedComponent := by
  classical
  exact Finset.univ.filter (G.IsAllGoodPackingComponent S)

@[simp]
theorem mem_allGoodPackingComponents_iff
    (G : SimpleGraph V) {S : Finset (Finset V)}
    {C : (packingIntersectionGraph S).ConnectedComponent} :
    C ∈ G.allGoodPackingComponents S ↔
      G.IsAllGoodPackingComponent S C := by
  classical
  simp [allGoodPackingComponents]

/-- The numerical one-unit deficit attached to an all-good component. -/
noncomputable def allGoodComponentIndicator (G : SimpleGraph V)
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) : ℕ := by
  classical
  exact if G.IsAllGoodPackingComponent S C then 1 else 0

/-- A component is all-good exactly when its bad-triangle slice is empty. -/
theorem isAllGoodPackingComponent_iff_badTriangles_empty
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    G.IsAllGoodPackingComponent S C ↔
      G.badTrianglesInComponent S C = ∅ := by
  classical
  constructor
  · intro hAllGood
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t htBad
    have htData := Finset.mem_inter.mp htBad
    have htGood := hAllGood htData.1
    exact Finset.disjoint_left.mp (G.disjoint_good_bad S)
      htGood htData.2
  · intro hBadEmpty t htC
    have htS := packingComponentTriangles_subset C htC
    have htPartition :
        t ∈ G.goodPackingTriangles S ∨
          t ∈ G.badPackingTriangles S := by
      have hEq := congrArg (fun Q : Finset (Finset V) ↦ t ∈ Q)
        (G.good_union_bad_eq S)
      simpa only [Finset.mem_union] using hEq.mpr htS
    exact htPartition.resolve_right (fun htBad ↦ by
      have : t ∈ G.badTrianglesInComponent S C :=
        Finset.mem_inter.mpr ⟨htC, htBad⟩
      simpa [hBadEmpty] using this)

/-- The global bad-triangle family is the disjoint union of its component
slices. -/
theorem biUnion_badTrianglesInComponent
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    Finset.univ.biUnion (G.badTrianglesInComponent S) =
      G.badPackingTriangles S := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨C, _, htC⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_inter.mp htC).2
  · intro htBad
    have htS := (G.mem_badPackingTriangles_iff.mp htBad).1
    let q : {p : Finset V // p ∈ S} := ⟨t, htS⟩
    let C := (packingIntersectionGraph S).connectedComponentMk q
    have hqC : q ∈ C.supp := (C.mem_supp_iff q).mpr rfl
    have htC : t ∈ packingComponentTriangles S C :=
      mem_packingComponentTriangles_iff.mpr ⟨⟨q, hqC⟩, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨C, Finset.mem_univ C, Finset.mem_inter.mpr ⟨htC, htBad⟩⟩

/-- Bad-triangle component slices are pairwise disjoint. -/
theorem pairwiseDisjoint_badTrianglesInComponent
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    (Set.univ : Set
      (packingIntersectionGraph S).ConnectedComponent).PairwiseDisjoint
        (G.badTrianglesInComponent S) := by
  classical
  intro C _ D _ hCD
  change Disjoint (G.badTrianglesInComponent S C)
    (G.badTrianglesInComponent S D)
  exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
    (pairwiseDisjoint_packingComponentTriangles S
      (Set.mem_univ C) (Set.mem_univ D) hCD)

/-- Bad-triangle slice cardinalities sum to the global bad-triangle count. -/
theorem sum_card_badTrianglesInComponent
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    ∑ C : (packingIntersectionGraph S).ConnectedComponent,
        (G.badTrianglesInComponent S C).card =
      (G.badPackingTriangles S).card := by
  classical
  have hcard := congrArg Finset.card (G.biUnion_badTrianglesInComponent S)
  rw [Finset.card_biUnion (by
    simpa using G.pairwiseDisjoint_badTrianglesInComponent S)] at hcard
  simpa using hcard

/-- The local component bound with one extra unit exactly for an all-good
component. -/
theorem card_componentSupport_le_with_allGood_indicator
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    (packingComponentVertexSupport S C).card ≤
      2 * (packingComponentTriangles S C).card +
        (G.badTrianglesInComponent S C).card +
        G.allGoodComponentIndicator S C := by
  classical
  by_cases hAllGood : G.IsAllGoodPackingComponent S C
  · have hbound := card_componentSupport_le_vertexCharge_add_one hS C
    simp [allGoodComponentIndicator, hAllGood]
    omega
  · have hBadNonempty : (G.badTrianglesInComponent S C).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      exact hAllGood
        ((G.isAllGoodPackingComponent_iff_badTriangles_empty C).mpr hEmpty)
    have hbound := card_componentSupport_le_vertexCharge_of_bad_nonempty
      hS C hBadNonempty
    simp [allGoodComponentIndicator, hAllGood]
    exact hbound

/-- Summing the component bounds charges the packing support by two units per
packed triangle, one per bad triangle, and one per all-good component. -/
theorem card_triangleFamilyVertexSupport_le_discharge_base
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S) :
    (triangleFamilyVertexSupport S).card ≤
      2 * S.card + (G.badPackingTriangles S).card +
        (G.allGoodPackingComponents S).card := by
  classical
  have hsum :
      (∑ C : (packingIntersectionGraph S).ConnectedComponent,
          (packingComponentVertexSupport S C).card) ≤
        ∑ C : (packingIntersectionGraph S).ConnectedComponent,
          (2 * (packingComponentTriangles S C).card +
            (G.badTrianglesInComponent S C).card +
            G.allGoodComponentIndicator S C) := by
    apply Finset.sum_le_sum
    intro C _
    exact G.card_componentSupport_le_with_allGood_indicator hS C
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_card_packingComponentTriangles,
    G.sum_card_badTrianglesInComponent] at hsum
  have hIndicator :
      (∑ C : (packingIntersectionGraph S).ConnectedComponent,
          G.allGoodComponentIndicator S C) =
        (G.allGoodPackingComponents S).card := by
    classical
    simp [allGoodComponentIndicator, allGoodPackingComponents]
  rw [hIndicator] at hsum
  calc
    (triangleFamilyVertexSupport S).card =
        ∑ C : (packingIntersectionGraph S).ConnectedComponent,
          (packingComponentVertexSupport S C).card :=
      card_triangleFamilyVertexSupport_eq_sum_components S
    _ ≤ _ := hsum

/-- All-good components that contain a pretty-good packed triangle. -/
noncomputable def transferPackingComponents (G : SimpleGraph V)
    (S : Finset (Finset V)) :
    Finset (packingIntersectionGraph S).ConnectedComponent := by
  classical
  exact (G.allGoodPackingComponents S).filter
    (G.PackingComponentHasPrettyGood S)

/-- All-good components containing only excellent packed triangles. -/
noncomputable def excellentOnlyPackingComponents (G : SimpleGraph V)
    (S : Finset (Finset V)) :
    Finset (packingIntersectionGraph S).ConnectedComponent := by
  classical
  exact (G.allGoodPackingComponents S).filter
    (fun C ↦ ¬G.PackingComponentHasPrettyGood S C)

@[simp]
theorem mem_transferPackingComponents_iff
    (G : SimpleGraph V) {S : Finset (Finset V)}
    {C : (packingIntersectionGraph S).ConnectedComponent} :
    C ∈ G.transferPackingComponents S ↔
      G.IsAllGoodPackingComponent S C ∧
      G.PackingComponentHasPrettyGood S C := by
  classical
  simp [transferPackingComponents]

@[simp]
theorem mem_excellentOnlyPackingComponents_iff
    (G : SimpleGraph V) {S : Finset (Finset V)}
    {C : (packingIntersectionGraph S).ConnectedComponent} :
    C ∈ G.excellentOnlyPackingComponents S ↔
      G.IsAllGoodPackingComponent S C ∧
      ¬G.PackingComponentHasPrettyGood S C := by
  classical
  simp [excellentOnlyPackingComponents]

theorem disjoint_transfer_excellentOnly
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    Disjoint (G.transferPackingComponents S)
      (G.excellentOnlyPackingComponents S) := by
  classical
  rw [Finset.disjoint_left]
  intro C hTransfer hExcellent
  have hT := G.mem_transferPackingComponents_iff.mp hTransfer
  have hE := G.mem_excellentOnlyPackingComponents_iff.mp hExcellent
  exact hE.2 hT.2

theorem card_transfer_add_card_excellentOnly
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    (G.transferPackingComponents S).card +
      (G.excellentOnlyPackingComponents S).card =
        (G.allGoodPackingComponents S).card := by
  classical
  simpa [transferPackingComponents, excellentOnlyPackingComponents] using
    (Finset.card_filter_add_card_filter_not
      (s := G.allGoodPackingComponents S)
      (p := G.PackingComponentHasPrettyGood S))

/-- Every all-good component has a canonical-kind residual representative:
`V₂` in a transfer component and `V₁` otherwise. -/
theorem exists_componentResidualVertex
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllGood : G.IsAllGoodPackingComponent S C) :
    ∃ z,
      z ∈ packingComponentVertexSupport S C ∧
      ((G.PackingComponentHasPrettyGood S C ∧
          z ∈ G.prettyGoodResidualVertices S) ∨
        (¬G.PackingComponentHasPrettyGood S C ∧
          z ∈ G.excellentResidualVertices S)) := by
  classical
  by_cases hPretty : G.PackingComponentHasPrettyGood S C
  · obtain ⟨z, hzC, hzResidual⟩ :=
      G.exists_prettyGoodResidualVertex_in_component hS hNoK4 C hPretty
    exact ⟨z, hzC, Or.inl ⟨hPretty, hzResidual⟩⟩
  · have hAllExcellent :=
      G.isAllExcellent_of_isAllGood_of_not_hasPrettyGood C hAllGood hPretty
    obtain ⟨z, hzC, hzResidual⟩ :=
      G.exists_excellentResidualVertex_in_allExcellent_component
        hS hNoK4 C hAllExcellent
    exact ⟨z, hzC, Or.inr ⟨hPretty, hzResidual⟩⟩

/-- The selected residual representative of an all-good component. -/
noncomputable def componentResidualVertex
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.allGoodPackingComponents S}) : V :=
  Classical.choose (G.exists_componentResidualVertex hS hNoK4 C.1
    (G.mem_allGoodPackingComponents_iff.mp C.2))

theorem componentResidualVertex_spec
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.allGoodPackingComponents S}) :
    G.componentResidualVertex hS hNoK4 C ∈
        packingComponentVertexSupport S C.1 ∧
      ((G.PackingComponentHasPrettyGood S C.1 ∧
          G.componentResidualVertex hS hNoK4 C ∈
            G.prettyGoodResidualVertices S) ∨
        (¬G.PackingComponentHasPrettyGood S C.1 ∧
          G.componentResidualVertex hS hNoK4 C ∈
            G.excellentResidualVertices S)) :=
  Classical.choose_spec (G.exists_componentResidualVertex hS hNoK4 C.1
    (G.mem_allGoodPackingComponents_iff.mp C.2))

/-- Residual representatives from distinct components are distinct. -/
theorem componentResidualVertex_injective
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    Function.Injective (G.componentResidualVertex hS hNoK4) := by
  classical
  intro C D hEq
  apply Subtype.ext
  by_contra hCD
  have hdis := disjoint_packingComponentVertexSupport hCD
  have hzC := (G.componentResidualVertex_spec hS hNoK4 C).1
  have hzD := (G.componentResidualVertex_spec hS hNoK4 D).1
  exact Finset.disjoint_left.mp hdis hzC (hEq ▸ hzD)

/-- The selected residual vertices, one for each all-good component. -/
noncomputable def componentResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) : Finset V :=
  Finset.univ.image (G.componentResidualVertex hS hNoK4)

theorem card_componentResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (G.componentResidualVertices hS hNoK4).card =
      (G.allGoodPackingComponents S).card := by
  classical
  rw [componentResidualVertices,
    Finset.card_image_iff.mpr
      (G.componentResidualVertex_injective hS hNoK4).injOn,
    Finset.card_univ]
  exact Fintype.card_coe _

/-- The residual representative of a transfer component. -/
noncomputable def transferResidualVertex
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.transferPackingComponents S}) : V :=
  G.componentResidualVertex hS hNoK4
    ⟨C.1, G.mem_allGoodPackingComponents_iff.mpr
      (G.mem_transferPackingComponents_iff.mp C.2).1⟩

theorem transferResidualVertex_mem
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.transferPackingComponents S}) :
    G.transferResidualVertex hS hNoK4 C ∈
        packingComponentVertexSupport S C.1 ∧
      G.transferResidualVertex hS hNoK4 C ∈
        G.prettyGoodResidualVertices S := by
  have hspec := G.componentResidualVertex_spec hS hNoK4
    ⟨C.1, G.mem_allGoodPackingComponents_iff.mpr
      (G.mem_transferPackingComponents_iff.mp C.2).1⟩
  refine ⟨hspec.1, ?_⟩
  rcases hspec.2 with hPretty | hExcellent
  · exact hPretty.2
  · exact (hExcellent.1
      (G.mem_transferPackingComponents_iff.mp C.2).2).elim

/-- The residual representative of an all-excellent component. -/
noncomputable def excellentResidualVertex
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.excellentOnlyPackingComponents S}) : V :=
  G.componentResidualVertex hS hNoK4
    ⟨C.1, G.mem_allGoodPackingComponents_iff.mpr
      (G.mem_excellentOnlyPackingComponents_iff.mp C.2).1⟩

theorem excellentResidualVertex_mem
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.excellentOnlyPackingComponents S}) :
    G.excellentResidualVertex hS hNoK4 C ∈
        packingComponentVertexSupport S C.1 ∧
      G.excellentResidualVertex hS hNoK4 C ∈
        G.excellentResidualVertices S := by
  have hspec := G.componentResidualVertex_spec hS hNoK4
    ⟨C.1, G.mem_allGoodPackingComponents_iff.mpr
      (G.mem_excellentOnlyPackingComponents_iff.mp C.2).1⟩
  refine ⟨hspec.1, ?_⟩
  rcases hspec.2 with hPretty | hExcellent
  · exact ((G.mem_excellentOnlyPackingComponents_iff.mp C.2).2
      hPretty.1).elim
  · exact hExcellent.2

/-- The selected `V₂` residual vertices. -/
noncomputable def transferResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) : Finset V :=
  Finset.univ.image (G.transferResidualVertex hS hNoK4)

/-- The selected `V₁` residual vertices. -/
noncomputable def excellentResidualVertexSet
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) : Finset V :=
  Finset.univ.image (G.excellentResidualVertex hS hNoK4)

theorem transferResidualVertex_injective
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    Function.Injective (G.transferResidualVertex hS hNoK4) := by
  intro C D hEq
  apply Subtype.ext
  have hbase := G.componentResidualVertex_injective hS hNoK4
  have hSubtype :
      (⟨C.1, G.mem_allGoodPackingComponents_iff.mpr
        (G.mem_transferPackingComponents_iff.mp C.2).1⟩ :
          {C // C ∈ G.allGoodPackingComponents S}) =
      ⟨D.1, G.mem_allGoodPackingComponents_iff.mpr
        (G.mem_transferPackingComponents_iff.mp D.2).1⟩ :=
    hbase hEq
  exact congrArg
    (fun X : {C // C ∈ G.allGoodPackingComponents S} ↦ X.1) hSubtype

theorem excellentResidualVertex_injective
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    Function.Injective (G.excellentResidualVertex hS hNoK4) := by
  intro C D hEq
  apply Subtype.ext
  have hbase := G.componentResidualVertex_injective hS hNoK4
  have hSubtype :
      (⟨C.1, G.mem_allGoodPackingComponents_iff.mpr
        (G.mem_excellentOnlyPackingComponents_iff.mp C.2).1⟩ :
          {C // C ∈ G.allGoodPackingComponents S}) =
      ⟨D.1, G.mem_allGoodPackingComponents_iff.mpr
        (G.mem_excellentOnlyPackingComponents_iff.mp D.2).1⟩ :=
    hbase hEq
  exact congrArg
    (fun X : {C // C ∈ G.allGoodPackingComponents S} ↦ X.1) hSubtype

theorem card_transferResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (G.transferResidualVertices hS hNoK4).card =
      (G.transferPackingComponents S).card := by
  classical
  rw [transferResidualVertices,
    Finset.card_image_iff.mpr
      (G.transferResidualVertex_injective hS hNoK4).injOn,
    Finset.card_univ]
  exact Fintype.card_coe _

theorem card_excellentResidualVertexSet
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (G.excellentResidualVertexSet hS hNoK4).card =
      (G.excellentOnlyPackingComponents S).card := by
  classical
  rw [excellentResidualVertexSet,
    Finset.card_image_iff.mpr
      (G.excellentResidualVertex_injective hS hNoK4).injOn,
    Finset.card_univ]
  exact Fintype.card_coe _

theorem transferResidualVertices_subset_prettyGoodResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    G.transferResidualVertices hS hNoK4 ⊆
      G.prettyGoodResidualVertices S := by
  classical
  intro z hz
  obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hz
  exact (G.transferResidualVertex_mem hS hNoK4 C).2

theorem excellentResidualVertexSet_subset_excellentResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    G.excellentResidualVertexSet hS hNoK4 ⊆
      G.excellentResidualVertices S := by
  classical
  intro z hz
  obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hz
  exact (G.excellentResidualVertex_mem hS hNoK4 C).2

/-- The selected local transfer witness of a transfer component. -/
noncomputable def selectedComponentTransferWitness
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.transferPackingComponents S}) :
    G.ComponentTransferWitness S C.1
      (G.transferResidualVertex hS hNoK4 C) :=
  Classical.choice (G.nonempty_componentTransferWitness hS C.1
    (G.mem_transferPackingComponents_iff.mp C.2).1
    (G.transferResidualVertex_mem hS hNoK4 C).1
    (G.transferResidualVertex_mem hS hNoK4 C).2)

/-- The two labelled edges spent in one selected component transfer. -/
noncomputable def componentTransferEdges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.transferPackingComponents S}) : Finset (Finset V) :=
  let W := G.selectedComponentTransferWitness hS hNoK4 C
  {W.firstEdge, W.secondEdge}

/-- The spanner credited by one selected component transfer. -/
noncomputable def componentTransferSpanner
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.transferPackingComponents S}) : V :=
  (G.selectedComponentTransferWitness hS hNoK4 C).spanner

/-- All labelled edges depleted by the selected component transfers. -/
noncomputable def depletedTransferEdges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    Finset (Finset V) :=
  Finset.univ.biUnion (G.componentTransferEdges hS hNoK4)

/-- All outside spanners credited by the selected component transfers. -/
noncomputable def creditedTransferVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) : Finset V :=
  Finset.univ.image (G.componentTransferSpanner hS hNoK4)

/-- Complete data attached to either edge of a selected transfer. -/
theorem componentTransferEdge_data
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.transferPackingComponents S})
    {e : Finset V} (he : e ∈ G.componentTransferEdges hS hNoK4 C) :
    e ∈ G.labelledPackingEdges S ∧
      ∃ t ∈ packingComponentTriangles S C.1,
        t ∈ G.prettyGoodPackingTriangles S ∧ e ⊆ t ∧
        G.packingEdgeSpanners S e =
          {G.componentTransferSpanner hS hNoK4 C} := by
  classical
  let W := G.selectedComponentTransferWitness hS hNoK4 C
  change e ∈ ({W.firstEdge, W.secondEdge} : Finset (Finset V)) at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨W.first_labelled, W.firstTriangle, W.first_mem_component,
      W.first_prettyGood, W.first_subset, W.first_spanners⟩
  · exact ⟨W.second_labelled, W.secondTriangle, W.second_mem_component,
      W.second_prettyGood, W.second_subset, W.second_spanners⟩

theorem card_componentTransferEdges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (C : {C : (packingIntersectionGraph S).ConnectedComponent //
      C ∈ G.transferPackingComponents S}) :
    (G.componentTransferEdges hS hNoK4 C).card = 2 := by
  classical
  let W := G.selectedComponentTransferWitness hS hNoK4 C
  change ({W.firstEdge, W.secondEdge} : Finset (Finset V)).card = 2
  simp [W.edges_ne]

/-- Transfer-edge pairs belonging to distinct packing components are
disjoint. -/
theorem pairwiseDisjoint_componentTransferEdges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (Set.univ : Set {C :
      (packingIntersectionGraph S).ConnectedComponent //
        C ∈ G.transferPackingComponents S}).PairwiseDisjoint
      (G.componentTransferEdges hS hNoK4) := by
  classical
  intro C _ D _ hCD
  change Disjoint (G.componentTransferEdges hS hNoK4 C)
    (G.componentTransferEdges hS hNoK4 D)
  rw [Finset.disjoint_left]
  intro e heC heD
  have hCdata := G.componentTransferEdge_data hS hNoK4 C heC
  have hDdata := G.componentTransferEdge_data hS hNoK4 D heD
  obtain ⟨t, htC, _, heSubT, _⟩ := hCdata.2
  obtain ⟨p, hpD, _, heSubP, _⟩ := hDdata.2
  have heCard : e.card = 2 := by
    obtain ⟨_, _, _, hcard⟩ := mem_triangleFamilyEdges_iff.mp
      (G.mem_labelledPackingEdges_iff.mp hCdata.1).1
    exact hcard
  obtain ⟨a, hae⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
  have hCDval : C.1 ≠ D.1 := fun h ↦ hCD (Subtype.ext h)
  exact Finset.disjoint_left.mp
    (disjoint_packingComponentVertexSupport hCDval)
    (Finset.mem_biUnion.mpr ⟨t, htC, heSubT hae⟩)
    (Finset.mem_biUnion.mpr ⟨p, hpD, heSubP hae⟩)

/-- Exactly two labelled edges are depleted per transfer component. -/
theorem card_depletedTransferEdges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (G.depletedTransferEdges hS hNoK4).card =
      2 * (G.transferPackingComponents S).card := by
  classical
  rw [depletedTransferEdges, Finset.card_biUnion (by
    simpa using G.pairwiseDisjoint_componentTransferEdges hS hNoK4)]
  simp_rw [G.card_componentTransferEdges hS hNoK4]
  simp [Nat.mul_comm]

/-- The canonical ledger produced by all transfer components. -/
noncomputable def canonicalTransferLedger
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    G.LabelledTransferLedger S := by
  classical
  refine {
    depletedEdges := G.depletedTransferEdges hS hNoK4
    creditedVertices := G.creditedTransferVertices hS hNoK4
    depleted_subset := ?_
    depleted_spanners_credited := ?_
    depleted_owned_by_prettyGood := ?_
  }
  · intro e he
    obtain ⟨C, _, heC⟩ := Finset.mem_biUnion.mp he
    exact (G.componentTransferEdge_data hS hNoK4 C heC).1
  · intro e he z hz
    obtain ⟨C, _, heC⟩ := Finset.mem_biUnion.mp he
    have hdata := G.componentTransferEdge_data hS hNoK4 C heC
    have hzEq : z = G.componentTransferSpanner hS hNoK4 C := by
      have : z ∈ ({G.componentTransferSpanner hS hNoK4 C} : Finset V) := by
        simpa [hdata.2.choose_spec.2.2.2] using hz
      simpa using this
    exact Finset.mem_image.mpr ⟨C, Finset.mem_univ C, hzEq.symm⟩
  · intro e he
    obtain ⟨C, _, heC⟩ := Finset.mem_biUnion.mp he
    have hdata := G.componentTransferEdge_data hS hNoK4 C heC
    exact ⟨hdata.2.choose, hdata.2.choose_spec.2.1,
      hdata.2.choose_spec.2.2.1⟩

/-- Credited vertices are outside the packing support. -/
theorem creditedTransferVertices_subset_outside
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    G.creditedTransferVertices hS hNoK4 ⊆ outsidePackingVertices S := by
  classical
  intro z hz
  obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hz
  let W := G.selectedComponentTransferWitness hS hNoK4 C
  have hmem : W.spanner ∈ G.packingEdgeSpanners S W.firstEdge := by
    rw [W.first_spanners]
    simp
  exact mem_outsidePackingVertices_iff.mpr
    (G.mem_packingEdgeSpanners_iff.mp hmem).1

/-- At most one outside vertex is credited per transfer component. -/
theorem card_creditedTransferVertices_le
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (G.creditedTransferVertices hS hNoK4).card ≤
      (G.transferPackingComponents S).card := by
  classical
  calc
    (G.creditedTransferVertices hS hNoK4).card ≤
        (Finset.univ : Finset {C :
          (packingIntersectionGraph S).ConnectedComponent //
            C ∈ G.transferPackingComponents S}).card := by
      exact Finset.card_image_le
    _ = (G.transferPackingComponents S).card := by
      rw [Finset.card_univ]
      exact Fintype.card_coe _

/-- The outside vertices whose charge was not consumed by a component
transfer. -/
noncomputable def uncreditedOutsideVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) : Finset V :=
  outsidePackingVertices S \ G.creditedTransferVertices hS hNoK4

/-- The independent residual family used in the final Hall argument. -/
noncomputable def finalResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) : Finset V :=
  G.excellentResidualVertexSet hS hNoK4 ∪
    G.uncreditedOutsideVertices hS hNoK4

/-- A selected excellent residual vertex still lies in the original packing
support. -/
theorem excellentResidualVertexSet_subset_packingSupport
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    G.excellentResidualVertexSet hS hNoK4 ⊆
      triangleFamilyVertexSupport S := by
  classical
  intro z hz
  have hzExcellent :=
    G.excellentResidualVertexSet_subset_excellentResidualVertices
      hS hNoK4 hz
  obtain ⟨t, htExcellent, hzt⟩ := Finset.mem_biUnion.mp
    (G.mem_excellentResidualVertices_iff.mp hzExcellent).1
  have htS := (G.mem_goodPackingTriangles_iff.mp
    (G.mem_excellentPackingTriangles_iff.mp htExcellent).1).1
  exact Finset.mem_biUnion.mpr ⟨t, htS, hzt⟩

theorem disjoint_excellentResidualVertexSet_uncreditedOutside
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    Disjoint (G.excellentResidualVertexSet hS hNoK4)
      (G.uncreditedOutsideVertices hS hNoK4) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzExcellent hzOutside
  have hzSupport :=
    G.excellentResidualVertexSet_subset_packingSupport hS hNoK4 hzExcellent
  exact (mem_outsidePackingVertices_iff.mp
    (Finset.mem_sdiff.mp hzOutside).1) hzSupport

/-- Exact size of the final residual family. -/
theorem card_finalResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (G.finalResidualVertices hS hNoK4).card =
      (G.excellentOnlyPackingComponents S).card +
        ((outsidePackingVertices S).card -
          (G.creditedTransferVertices hS hNoK4).card) := by
  classical
  rw [finalResidualVertices,
    Finset.card_union_of_disjoint
      (G.disjoint_excellentResidualVertexSet_uncreditedOutside hS hNoK4),
    G.card_excellentResidualVertexSet hS hNoK4,
    uncreditedOutsideVertices,
    Finset.card_sdiff_of_subset
      (G.creditedTransferVertices_subset_outside hS hNoK4)]

/-- Every supported vertex spans the other two vertices of one of its
triangles. -/
theorem exists_spans_of_mem_triangleSupportVertices
    (G : SimpleGraph V) {z : V}
    (hz : z ∈ G.triangleSupportVertices) :
    ∃ e : Finset V, G.Spans z e := by
  classical
  obtain ⟨t, ht, hzt⟩ := G.mem_triangleSupportVertices_iff.mp hz
  refine ⟨t.erase z, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hzt,
      G.card_eq_three_of_mem_triangles ht]
  · simpa [Finset.insert_erase hzt] using ht

/-- The final residual family avoids all labelled packing-edge endpoints. -/
theorem finalResidualVertices_disjoint_labelledPackingVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    Disjoint (G.finalResidualVertices hS hNoK4)
      (G.labelledPackingVertices S) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzFinal hzLabelled
  rcases Finset.mem_union.mp hzFinal with hzExcellent | hzOutside
  · have hzResidual :=
      G.excellentResidualVertexSet_subset_excellentResidualVertices
        hS hNoK4 hzExcellent
    exact (G.mem_excellentResidualVertices_iff.mp hzResidual).2.1 hzLabelled
  · have hzSupport := G.labelledPackingVertices_subset_triangleFamilyVertexSupport
      S hzLabelled
    exact (mem_outsidePackingVertices_iff.mp
      (Finset.mem_sdiff.mp hzOutside).1) hzSupport

/-- The final residual family inherits the global residual independence
theorem. -/
theorem isIndepSet_finalResidualVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (hTriangleSupport : G.triangleSupport = G) :
    G.IsIndepSet (G.finalResidualVertices hS hNoK4 : Set V) := by
  apply (G.isIndepSet_outside_union_excellentResidualVertices
    hS hTriangleSupport).mono
  intro z hz
  rcases Finset.mem_union.mp hz with hzExcellent | hzOutside
  · exact Finset.mem_union_right _
      (G.excellentResidualVertexSet_subset_excellentResidualVertices
        hS hNoK4 hzExcellent)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hzOutside).1

/-- The canonical ledger has exactly the labelled units left after spending
two units per transfer component. -/
theorem card_canonicalTransferLedger_remainingEdges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q) :
    (G.canonicalTransferLedger hS hNoK4).remainingEdges.card =
      (G.labelledPackingEdges S).card -
        2 * (G.transferPackingComponents S).card := by
  classical
  rw [LabelledTransferLedger.remainingEdges,
    Finset.card_sdiff_of_subset
      (G.canonicalTransferLedger hS hNoK4).depleted_subset]
  change (G.labelledPackingEdges S).card -
      (G.depletedTransferEdges hS hNoK4).card = _
  rw [G.card_depletedTransferEdges hS hNoK4]

/-- Every edge spanned by a final residual vertex retains its ledger unit. -/
theorem mem_canonicalTransferLedger_remainingEdges_of_finalResidual
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (hSplit : G.IsSplitNormal)
    {z : V} (hz : z ∈ G.finalResidualVertices hS hNoK4)
    {e : Finset V} (hze : G.Spans z e) :
    e ∈ (G.canonicalTransferLedger hS hNoK4).remainingEdges := by
  classical
  rcases Finset.mem_union.mp hz with hzExcellent | hzOutside
  · obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hzExcellent
    have hCdata := G.mem_excellentOnlyPackingComponents_iff.mp C.2
    have hAllExcellent :=
      G.isAllExcellent_of_isAllGood_of_not_hasPrettyGood
        C.1 hCdata.1 hCdata.2
    have hzData := G.excellentResidualVertex_mem hS hNoK4 C
    have hzNotLabelled :
        G.excellentResidualVertex hS hNoK4 C ∉
          G.labelledPackingVertices S :=
      (G.mem_excellentResidualVertices_iff.mp hzData.2).2.1
    exact (G.canonicalTransferLedger hS hNoK4).mem_remainingEdges_of_spans_internal
      hS hSplit C.1 hAllExcellent
        hzData.1 hzNotLabelled hze
  · have hzData := Finset.mem_sdiff.mp hzOutside
    apply (G.canonicalTransferLedger hS hNoK4).mem_remainingEdges_of_spans_outside_uncredited hS
      (mem_outsidePackingVertices_iff.mp hzData.1)
    · simpa [canonicalTransferLedger] using hzData.2
    · exact hze

/-- Absence of a nonempty crown turns the residual construction into the
numeric inequality needed by the discharge. -/
theorem card_finalResidualVertices_le_remainingEdges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (hSplit : G.IsSplitNormal)
    (hTriangleSupport : G.triangleSupport = G)
    (hEverySupported : ∀ z : V, z ∈ G.triangleSupportVertices)
    (hNoCrown : ¬∃ K : G.FatHeadCrown, K.headEdges.Nonempty) :
    (G.finalResidualVertices hS hNoK4).card ≤
      (G.canonicalTransferLedger hS hNoK4).remainingEdges.card := by
  apply G.card_le_remainingEdges_of_no_fatHeadCrown
    (G.canonicalTransferLedger hS hNoK4) hTriangleSupport
  · exact G.isIndepSet_finalResidualVertices hS hNoK4 hTriangleSupport
  · exact G.finalResidualVertices_disjoint_labelledPackingVertices hS hNoK4
  · intro z _
    exact G.exists_spans_of_mem_triangleSupportVertices (hEverySupported z)
  · intro z hz e hze
    exact G.mem_canonicalTransferLedger_remainingEdges_of_finalResidual
      hS hNoK4 hSplit hz hze
  · exact hNoCrown

/-- The packing support and its outside complement partition the finite
carrier. -/
theorem fintype_card_eq_packingSupport_add_outside
    (S : Finset (Finset V)) :
    Fintype.card V = (triangleFamilyVertexSupport S).card +
      (outsidePackingVertices S).card := by
  classical
  have hpartition := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (triangleFamilyVertexSupport S))
  simpa [outsidePackingVertices, Nat.add_comm] using hpartition.symm

/-- The complete analytic discharge: a supported split-normal graph with no
isolated `K₄` block and no nonempty fat-head crown has at most three vertices
per triangle of a support-maximal maximum packing. -/
theorem fintype_card_le_three_mul_packing_card
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    (hSplit : G.IsSplitNormal)
    (hTriangleSupport : G.triangleSupport = G)
    (hEverySupported : ∀ z : V, z ∈ G.triangleSupportVertices)
    (hNoCrown : ¬∃ K : G.FatHeadCrown, K.headEdges.Nonempty) :
    Fintype.card V ≤ 3 * S.card := by
  classical
  have hBase := G.card_triangleFamilyVertexSupport_le_discharge_base hS.1
  have hPartition := G.card_transfer_add_card_excellentOnly S
  have hCrown := G.card_finalResidualVertices_le_remainingEdges
    hS hNoK4 hSplit hTriangleSupport hEverySupported hNoCrown
  rw [G.card_finalResidualVertices hS hNoK4,
    G.card_canonicalTransferLedger_remainingEdges hS hNoK4] at hCrown
  have hCredit := G.card_creditedTransferVertices_le hS hNoK4
  have hCreditOutside := Finset.card_le_card
    (G.creditedTransferVertices_subset_outside hS hNoK4)
  have hSpent :
      2 * (G.transferPackingComponents S).card ≤
        (G.labelledPackingEdges S).card := by
    have hsub := Finset.card_le_card
      (G.canonicalTransferLedger hS hNoK4).depleted_subset
    change (G.depletedTransferEdges hS hNoK4).card ≤
      (G.labelledPackingEdges S).card at hsub
    rwa [G.card_depletedTransferEdges hS hNoK4] at hsub
  have hSources := G.card_labelled_add_card_bad_eq_card_packing
    hS hNoK4
  have hCarrier := fintype_card_eq_packingSupport_add_outside S
  omega

end SimpleGraph
