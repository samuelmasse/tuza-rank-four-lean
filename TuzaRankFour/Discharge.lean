import TuzaRankFour.KernelReduction
import TuzaRankFour.PackingSaturation

/-!
# Foundations for the twelve-vertex discharge

This file develops the packing-edge language used by the analytic order
bound.  A support-maximal maximum packing is already saturated against every
cardinality-increasing or support-increasing exchange, so the local discharge
proof can work directly with that extremal object.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph edges contained in members of a triangle family. -/
noncomputable def triangleFamilyEdges (P : Finset (Finset V)) :
    Finset (Finset V) :=
  P.biUnion fun t ↦ t.powersetCard 2

omit [Fintype V] in
@[simp]
theorem mem_triangleFamilyEdges_iff {P : Finset (Finset V)}
    {e : Finset V} :
    e ∈ triangleFamilyEdges P ↔
      ∃ t ∈ P, e ⊆ t ∧ e.card = 2 := by
  classical
  simp [triangleFamilyEdges]

/-- An outside vertex spans a packing edge when it forms a graph triangle
with the two endpoints of that edge. -/
def SpansPackingEdge (G : SimpleGraph V) (S : Finset (Finset V))
    (x : V) (e : Finset V) : Prop :=
  e ∈ triangleFamilyEdges S ∧ insert x e ∈ G.triangles

/-- Every triangle meets a maximum packing in a graph edge. -/
theorem exists_two_le_card_inter_of_isSupportMaximalPacking
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t : Finset V} (ht : t ∈ G.triangles) :
    ∃ q ∈ S, 2 ≤ (q ∩ t).card := by
  classical
  by_contra h
  push Not at h
  have hcompat : ∀ ⦃q⦄, q ∈ S → (q ∩ t).card ≤ 1 := by
    intro q hq
    have := h q hq
    omega
  have htNot : t ∉ S := by
    intro htS
    have hsmall := hcompat htS
    have htCard := G.card_eq_three_of_mem_triangles ht
    rw [Finset.inter_self, htCard] at hsmall
    omega
  have hpacking : G.IsTrianglePacking (insert t S) :=
    G.isTrianglePacking_insert hS.1 ht hcompat
  have hbound := G.card_le_trianglePackingNumber hpacking
  have hcard : (insert t S).card = S.card + 1 :=
    Finset.card_insert_of_notMem htNot
  rw [hcard, hS.2.1] at hbound
  omega

/-- If `x` is outside a support-maximal packing and lies in a triangle, then
it spans a two-element edge of that packing. -/
theorem exists_spansPackingEdge_of_outside
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {x : V} (hxOutside : x ∉ triangleFamilyVertexSupport S)
    {t : Finset V} (ht : t ∈ G.triangles) (hxt : x ∈ t) :
    ∃ e, G.SpansPackingEdge S x e := by
  classical
  obtain ⟨q, hqS, hinterLower⟩ :=
    G.exists_two_le_card_inter_of_isSupportMaximalPacking hS ht
  have hxq : x ∉ q := by
    intro hxq
    apply hxOutside
    exact Finset.mem_biUnion.mpr ⟨q, hqS, hxq⟩
  let e := q ∩ t
  have heSubErase : e ⊆ t.erase x := by
    intro y hy
    simp only [e, Finset.mem_inter] at hy
    exact Finset.mem_erase.mpr ⟨fun hyx ↦ hxq (hyx ▸ hy.1), hy.2⟩
  have htCard : t.card = 3 := G.card_eq_three_of_mem_triangles ht
  have hEraseCard : (t.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxt]
    omega
  have heCardUpper := Finset.card_le_card heSubErase
  have heCard : e.card = 2 := by
    change 2 ≤ e.card at hinterLower
    omega
  have heErase : e = t.erase x :=
    Finset.eq_of_subset_of_card_le heSubErase (by omega)
  have hInsert : insert x e = t := by
    rw [heErase, Finset.insert_erase hxt]
  refine ⟨e, ?_, ?_⟩
  · rw [mem_triangleFamilyEdges_iff]
    exact ⟨q, hqS, Finset.inter_subset_left, heCard⟩
  · simpa [hInsert] using ht

/-- In a graph where every vertex belongs to a triangle, each vertex outside
a support-maximal maximum packing spans one of its packing edges. -/
theorem exists_spansPackingEdge_of_mem_triangleSupportVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {x : V} (hxOutside : x ∉ triangleFamilyVertexSupport S)
    (hxSupported : x ∈ G.triangleSupportVertices) :
    ∃ e, G.SpansPackingEdge S x e := by
  obtain ⟨t, ht, hxt⟩ := G.mem_triangleSupportVertices_iff.mp hxSupported
  exact G.exists_spansPackingEdge_of_outside hS hxOutside ht hxt

/-- A two-element edge cannot belong to two distinct members of a triangle
packing. -/
theorem eq_of_mem_powersetCard_of_isTrianglePacking
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    {s t e : Finset V} (hs : s ∈ S) (ht : t ∈ S)
    (hes : e ∈ s.powersetCard 2) (het : e ∈ t.powersetCard 2) :
    s = t := by
  classical
  by_contra hst
  have hsmall := hS.2 hs ht hst
  have heSub : e ⊆ s ∩ t := by
    intro x hx
    simp only [Finset.mem_inter]
    exact ⟨(Finset.mem_powersetCard.mp hes).1 hx,
      (Finset.mem_powersetCard.mp het).1 hx⟩
  have hlarge := Finset.card_le_card heSub
  have heCard := (Finset.mem_powersetCard.mp hes).2
  omega

/-- The three edges contributed by distinct members of a triangle packing are
pairwise disjoint as elements of the edge family. -/
theorem pairwiseDisjoint_powersetCard_two_of_isTrianglePacking
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S) :
    (S : Set (Finset V)).PairwiseDisjoint fun t ↦ t.powersetCard 2 := by
  classical
  intro s hs t ht hst
  change Disjoint (s.powersetCard 2) (t.powersetCard 2)
  rw [Finset.disjoint_left]
  intro e hes het
  exact hst (G.eq_of_mem_powersetCard_of_isTrianglePacking hS hs ht hes het)

/-- A triangle packing of cardinality `k` has exactly `3k` distinct packing
edges. -/
theorem card_triangleFamilyEdges_of_isTrianglePacking
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S) :
    (triangleFamilyEdges S).card = 3 * S.card := by
  classical
  rw [triangleFamilyEdges,
    Finset.card_biUnion
      (G.pairwiseDisjoint_powersetCard_two_of_isTrianglePacking hS)]
  calc
    ∑ t ∈ S, (t.powersetCard 2).card = ∑ _t ∈ S, 3 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact G.card_powersetCard_two_of_triangle (hS.1 ht)
    _ = 3 * S.card := by simp [Nat.mul_comm]

/-- Any subfamily of a triangle packing is again a triangle packing. -/
theorem IsTrianglePacking.mono_family (G : SimpleGraph V)
    {P Q : Finset (Finset V)} (hP : G.IsTrianglePacking P)
    (hQP : Q ⊆ P) : G.IsTrianglePacking Q := by
  constructor
  · exact hQP.trans hP.1
  · intro s hs t ht hst
    exact hP.2 (hQP hs) (hQP ht) hst

/-- A retained packing triangle meets a replacement triangle supported on one
edge of the removed member and one outside vertex in at most one vertex. -/
theorem card_inter_insert_edge_le_one_of_outside
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    {q t e : Finset V} (hqS : q ∈ S) (htS : t ∈ S) (hqt : q ≠ t)
    (heSub : e ⊆ t) {x : V}
    (hxOutside : x ∉ triangleFamilyVertexSupport S) :
    (q ∩ insert x e).card ≤ 1 := by
  classical
  have hxq : x ∉ q := by
    intro hxq
    exact hxOutside (Finset.mem_biUnion.mpr ⟨q, hqS, hxq⟩)
  have hsub : q ∩ insert x e ⊆ q ∩ t := by
    intro z hz
    simp only [Finset.mem_inter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    rcases Finset.mem_insert.mp hz.2 with rfl | hze
    · exact (hxq hz.1).elim
    · exact heSub hze
  exact (Finset.card_le_card hsub).trans (hS.2 hqS htS hqt)

omit [Fintype V] in
/-- Replacement triangles built on distinct edges of the same packed
triangle and distinct outside vertices are edge-disjoint. -/
theorem card_inter_insert_edges_le_one_of_distinct_outside
    {t e f : Finset V}
    (he : e ∈ t.powersetCard 2) (hf : f ∈ t.powersetCard 2)
    (hef : e ≠ f) {x y : V} (hxy : x ≠ y)
    (hxt : x ∉ t) (hyt : y ∉ t) :
    (insert x e ∩ insert y f).card ≤ 1 := by
  classical
  have heSub := (Finset.mem_powersetCard.mp he).1
  have hfSub := (Finset.mem_powersetCard.mp hf).1
  have hsub : insert x e ∩ insert y f ⊆ e ∩ f := by
    intro z hz
    simp only [Finset.mem_inter] at hz ⊢
    rcases Finset.mem_insert.mp hz.1 with rfl | hze
    · rcases Finset.mem_insert.mp hz.2 with hxy' | hxf
      · exact (hxy hxy').elim
      · exact (hxt (hfSub hxf)).elim
    · rcases Finset.mem_insert.mp hz.2 with hyz | hzf
      · exact (hyt (heSub (hyz ▸ hze))).elim
      · exact ⟨hze, hzf⟩
  have hinter := card_inter_le_one_of_card_eq_two
    (Finset.mem_powersetCard.mp he).2
    (Finset.mem_powersetCard.mp hf).2 hef
  exact (Finset.card_le_card hsub).trans hinter

/-- Distinct labelled edges of one packing triangle cannot be spanned by
distinct outside vertices: otherwise replacing that member by the two
spanning triangles increases the packing cardinality. -/
theorem eq_of_spans_distinct_edges_of_isSupportMaximalPacking
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t e f : Finset V} (htS : t ∈ S)
    (he : e ∈ t.powersetCard 2) (hf : f ∈ t.powersetCard 2)
    (hef : e ≠ f) {x y : V}
    (hxOutside : x ∉ triangleFamilyVertexSupport S)
    (hyOutside : y ∉ triangleFamilyVertexSupport S)
    (hxTriangle : insert x e ∈ G.triangles)
    (hyTriangle : insert y f ∈ G.triangles) :
    x = y := by
  classical
  by_contra hxy
  let qx := insert x e
  let qy := insert y f
  let R := S.erase t
  have hRsub : R ⊆ S := Finset.erase_subset _ _
  have hRpacking : G.IsTrianglePacking R := hS.1.mono_family G hRsub
  have hxt : x ∉ t := by
    intro hxt
    exact hxOutside (Finset.mem_biUnion.mpr ⟨t, htS, hxt⟩)
  have hyt : y ∉ t := by
    intro hyt
    exact hyOutside (Finset.mem_biUnion.mpr ⟨t, htS, hyt⟩)
  have hqxCompat : ∀ ⦃q⦄, q ∈ R → (q ∩ qx).card ≤ 1 := by
    intro q hq
    exact G.card_inter_insert_edge_le_one_of_outside hS.1
      (hRsub hq) htS (Finset.ne_of_mem_erase hq)
      (Finset.mem_powersetCard.mp he).1 hxOutside
  have hqyCompatR : ∀ ⦃q⦄, q ∈ R → (q ∩ qy).card ≤ 1 := by
    intro q hq
    exact G.card_inter_insert_edge_le_one_of_outside hS.1
      (hRsub hq) htS (Finset.ne_of_mem_erase hq)
      (Finset.mem_powersetCard.mp hf).1 hyOutside
  have hqxqy : (qx ∩ qy).card ≤ 1 := by
    exact card_inter_insert_edges_le_one_of_distinct_outside he hf hef hxy hxt hyt
  have hqxPacking : G.IsTrianglePacking (insert qx R) :=
    G.isTrianglePacking_insert hRpacking hxTriangle hqxCompat
  have hqyCompat : ∀ ⦃q⦄, q ∈ insert qx R → (q ∩ qy).card ≤ 1 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqR
    · exact hqxqy
    · exact hqyCompatR hqR
  have hPpacking : G.IsTrianglePacking (insert qy (insert qx R)) :=
    G.isTrianglePacking_insert hqxPacking hyTriangle hqyCompat
  have hqxNotR : qx ∉ R := by
    intro hqxR
    have hqxS := hRsub hqxR
    apply hxOutside
    exact Finset.mem_biUnion.mpr ⟨qx, hqxS, by simp [qx]⟩
  have hqyNotR : qy ∉ R := by
    intro hqyR
    have hqyS := hRsub hqyR
    apply hyOutside
    exact Finset.mem_biUnion.mpr ⟨qy, hqyS, by simp [qy]⟩
  have hqyNeQx : qy ≠ qx := by
    intro hEq
    have hxQy : x ∈ qy := by simpa [hEq, qx]
    rcases Finset.mem_insert.mp hxQy with hxy' | hxf
    · exact hxy hxy'
    · exact hxt ((Finset.mem_powersetCard.mp hf).1 hxf)
  have hqyNot : qy ∉ insert qx R := by
    simpa [Finset.mem_insert, hqyNeQx, hqyNotR]
  have hcardR : R.card + 1 = S.card := by
    change (S.erase t).card + 1 = S.card
    rw [Finset.card_erase_of_mem htS]
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨t, htS⟩
    omega
  have hcardP : (insert qy (insert qx R)).card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem hqyNot,
      Finset.card_insert_of_notMem hqxNotR]
    omega
  have hbound := G.card_le_trianglePackingNumber hPpacking
  rw [hcardP, ← hS.2.1] at hbound
  omega

/-- Outside vertices spanning a fixed packing edge. -/
noncomputable def packingEdgeSpanners (G : SimpleGraph V)
    (S : Finset (Finset V)) (e : Finset V) : Finset V :=
  Finset.univ.filter fun x ↦
    x ∉ triangleFamilyVertexSupport S ∧ insert x e ∈ G.triangles

@[simp]
theorem mem_packingEdgeSpanners_iff (G : SimpleGraph V)
    {S : Finset (Finset V)} {e : Finset V} {x : V} :
    x ∈ G.packingEdgeSpanners S e ↔
      x ∉ triangleFamilyVertexSupport S ∧ insert x e ∈ G.triangles := by
  classical
  simp [packingEdgeSpanners]

/-- The labelled edges of a packing are precisely its edges with an outside
spanner. -/
noncomputable def labelledPackingEdges (G : SimpleGraph V)
    (S : Finset (Finset V)) : Finset (Finset V) :=
  (triangleFamilyEdges S).filter fun e ↦
    (G.packingEdgeSpanners S e).Nonempty

@[simp]
theorem mem_labelledPackingEdges_iff (G : SimpleGraph V)
    {S : Finset (Finset V)} {e : Finset V} :
    e ∈ G.labelledPackingEdges S ↔
      e ∈ triangleFamilyEdges S ∧
        (G.packingEdgeSpanners S e).Nonempty := by
  classical
  simp [labelledPackingEdges]

/-- If two different edges of one packed triangle are labelled, then every
spanner of either edge is the same vertex. -/
theorem eq_of_mem_spanners_of_distinct_edges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t e f : Finset V} (htS : t ∈ S)
    (he : e ∈ t.powersetCard 2) (hf : f ∈ t.powersetCard 2)
    (hef : e ≠ f) {x y : V}
    (hx : x ∈ G.packingEdgeSpanners S e)
    (hy : y ∈ G.packingEdgeSpanners S f) : x = y := by
  rw [G.mem_packingEdgeSpanners_iff] at hx hy
  exact G.eq_of_spans_distinct_edges_of_isSupportMaximalPacking hS htS
    he hf hef hx.1 hy.1 hx.2 hy.2

/-- The two nonempty spanner sets on distinct labelled edges of one packed
triangle coincide and are singletons. -/
theorem exists_common_unique_spanner_of_distinct_labelled_edges
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t e f : Finset V} (htS : t ∈ S)
    (he : e ∈ t.powersetCard 2) (hf : f ∈ t.powersetCard 2)
    (hef : e ≠ f)
    (heLabelled : e ∈ G.labelledPackingEdges S)
    (hfLabelled : f ∈ G.labelledPackingEdges S) :
    ∃ x, G.packingEdgeSpanners S e = {x} ∧
      G.packingEdgeSpanners S f = {x} := by
  classical
  obtain ⟨x, hx⟩ := (G.mem_labelledPackingEdges_iff.mp heLabelled).2
  obtain ⟨y, hy⟩ := (G.mem_labelledPackingEdges_iff.mp hfLabelled).2
  have hxy := G.eq_of_mem_spanners_of_distinct_edges hS htS he hf hef hx hy
  subst y
  refine ⟨x, ?_, ?_⟩
  · apply Finset.Subset.antisymm
    · intro z hz
      have hzx := G.eq_of_mem_spanners_of_distinct_edges hS htS he hf hef hz hy
      simp [hzx]
    · simp [hx]
  · apply Finset.Subset.antisymm
    · intro z hz
      have hxz := G.eq_of_mem_spanners_of_distinct_edges hS htS he hf hef hx hz
      simp [hxz]
    · simp [hy]

end SimpleGraph
