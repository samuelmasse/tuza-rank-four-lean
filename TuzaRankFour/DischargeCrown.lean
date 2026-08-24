import TuzaRankFour.DischargeClassification

/-!
# Crown-side foundations for the twelve-vertex discharge

The vertices outside a maximum packing are independent in a triangle-support
graph, and every one of their neighbours lies on a labelled packing edge.
These are the two local facts needed to turn a Hall-deficient spanner graph
into an actual fat-head crown.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices outside the support of a fixed triangle packing. -/
def outsidePackingVertices (S : Finset (Finset V)) : Finset V :=
  Finset.univ \ triangleFamilyVertexSupport S

@[simp]
theorem mem_outsidePackingVertices_iff
    {S : Finset (Finset V)} {v : V} :
    v ∈ outsidePackingVertices S ↔
      v ∉ triangleFamilyVertexSupport S := by
  classical
  simp [outsidePackingVertices]

/-- In a graph equal to its triangle support, vertices outside a maximum
packing form an independent set. -/
theorem isIndepSet_outsidePackingVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hTriangleSupport : G.triangleSupport = G) :
    G.IsIndepSet (outsidePackingVertices S : Set V) := by
  classical
  rw [G.isIndepSet_iff]
  intro u hu v hv huv huvAdj
  have huOutside : u ∉ triangleFamilyVertexSupport S := by simpa using hu
  have hvOutside : v ∉ triangleFamilyVertexSupport S := by simpa using hv
  have huvSupport : G.triangleSupport.Adj u v := by
    rw [hTriangleSupport]
    exact huvAdj
  obtain ⟨t, ht, hut, hvt, _⟩ := G.triangleSupport_adj_iff.mp huvSupport
  obtain ⟨q, hqS, hinterLower⟩ :=
    G.exists_two_le_card_inter_of_isSupportMaximalPacking hS ht
  have huq : u ∉ q := by
    intro huq
    exact huOutside (Finset.mem_biUnion.mpr ⟨q, hqS, huq⟩)
  have hvq : v ∉ q := by
    intro hvq
    exact hvOutside (Finset.mem_biUnion.mpr ⟨q, hqS, hvq⟩)
  have hsub : q ∩ t ⊆ (t.erase u).erase v := by
    intro z hz
    have hzData := Finset.mem_inter.mp hz
    exact Finset.mem_erase.mpr
      ⟨fun hzv ↦ hvq (hzv ▸ hzData.1),
        Finset.mem_erase.mpr
          ⟨fun hzu ↦ huq (hzu ▸ hzData.1), hzData.2⟩⟩
  have htCard : t.card = 3 := G.card_eq_three_of_mem_triangles ht
  have hEraseUCard : (t.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem hut, htCard]
  have hvEraseU : v ∈ t.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvt⟩
  have hEraseUVCard : ((t.erase u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hvEraseU, hEraseUCard]
  have hinterUpper := Finset.card_le_card hsub
  omega

/-- Every neighbour of an outside packing vertex is incident with a labelled
packing edge. -/
theorem neighbor_mem_labelledPackingVertices_of_outside
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hTriangleSupport : G.triangleSupport = G)
    {x y : V} (hxOutside : x ∉ triangleFamilyVertexSupport S)
    (hxy : G.Adj x y) :
    y ∈ G.labelledPackingVertices S := by
  classical
  have hxySupport : G.triangleSupport.Adj x y := by
    rw [hTriangleSupport]
    exact hxy
  obtain ⟨t, ht, hxt, hyt, hxyNe⟩ :=
    G.triangleSupport_adj_iff.mp hxySupport
  obtain ⟨q, hqS, hinterLower⟩ :=
    G.exists_two_le_card_inter_of_isSupportMaximalPacking hS ht
  let e := q ∩ t
  have hxq : x ∉ q := by
    intro hxq
    exact hxOutside (Finset.mem_biUnion.mpr ⟨q, hqS, hxq⟩)
  have heSubErase : e ⊆ t.erase x := by
    intro z hz
    have hzData := Finset.mem_inter.mp hz
    exact Finset.mem_erase.mpr
      ⟨fun hzx ↦ hxq (hzx ▸ hzData.1), hzData.2⟩
  have htCard : t.card = 3 := G.card_eq_three_of_mem_triangles ht
  have hEraseCard : (t.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxt, htCard]
  have heUpper := Finset.card_le_card heSubErase
  have heCard : e.card = 2 := by
    change 2 ≤ e.card at hinterLower
    omega
  have heErase : e = t.erase x :=
    Finset.eq_of_subset_of_card_le heSubErase (by omega)
  have hye : y ∈ e := by
    rw [heErase]
    exact Finset.mem_erase.mpr ⟨hxyNe.symm, hyt⟩
  have heFamily : e ∈ triangleFamilyEdges S := by
    rw [mem_triangleFamilyEdges_iff]
    exact ⟨q, hqS, Finset.inter_subset_left, heCard⟩
  have hInsert : insert x e = t := by
    rw [heErase, Finset.insert_erase hxt]
  have hxSpanner : x ∈ G.packingEdgeSpanners S e := by
    rw [G.mem_packingEdgeSpanners_iff]
    exact ⟨hxOutside, by simpa [hInsert] using ht⟩
  have heLabelled : e ∈ G.labelledPackingEdges S := by
    rw [G.mem_labelledPackingEdges_iff]
    exact ⟨heFamily, ⟨x, hxSpanner⟩⟩
  exact (G.mem_labelledPackingVertices_iff).mpr
    ⟨e, heLabelled, hye⟩

/-- Any two-edge set spanned by an outside vertex is necessarily a labelled
edge of the maximum packing. -/
theorem mem_labelledPackingEdges_of_spans_outside
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {x : V} (hxOutside : x ∉ triangleFamilyVertexSupport S)
    {e : Finset V} (hSpans : G.Spans x e) :
    e ∈ G.labelledPackingEdges S := by
  classical
  have heCard : e.card = 2 := hSpans.1
  have hxeCard : (insert x e).card = 3 :=
    G.card_eq_three_of_mem_triangles hSpans.2
  have hxe : x ∉ e := by
    intro hxe
    rw [Finset.insert_eq_of_mem hxe, hSpans.1] at hxeCard
    omega
  obtain ⟨q, hqS, hinterLower⟩ :=
    G.exists_two_le_card_inter_of_isSupportMaximalPacking hS hSpans.2
  have hxq : x ∉ q := by
    intro hxq
    exact hxOutside (Finset.mem_biUnion.mpr ⟨q, hqS, hxq⟩)
  have hsub : q ∩ insert x e ⊆ e := by
    intro v hv
    have hvData := Finset.mem_inter.mp hv
    rcases Finset.mem_insert.mp hvData.2 with rfl | hve
    · exact (hxq hvData.1).elim
    · exact hve
  have hinterUpper := Finset.card_le_card hsub
  have hinterCard : (q ∩ insert x e).card = 2 := by
    omega
  have hinterEq : q ∩ insert x e = e :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have heFamily : e ∈ triangleFamilyEdges S := by
    rw [mem_triangleFamilyEdges_iff]
    refine ⟨q, hqS, ?_, heCard⟩
    intro v hve
    have : v ∈ q ∩ insert x e := by
      rw [hinterEq]
      exact hve
    exact (Finset.mem_inter.mp this).1
  rw [G.mem_labelledPackingEdges_iff]
  refine ⟨heFamily, ⟨x, ?_⟩⟩
  rw [G.mem_packingEdgeSpanners_iff]
  exact ⟨hxOutside, hSpans.2⟩

/-- Labelled packing edges spanned by at least one member of a chosen vertex
set. -/
noncomputable def spannedLabelledEdges (G : SimpleGraph V)
    (S : Finset (Finset V)) (C : Finset V) : Finset (Finset V) := by
  classical
  exact (G.labelledPackingEdges S).filter fun e ↦
    ∃ c ∈ C, G.Spans c e

/-- For a set of outside vertices, `spannedLabelledEdges` is exactly the set
of all edges they span; maximality guarantees that no spanned edge is omitted
by the labelled-edge filter. -/
theorem mem_spannedLabelledEdges_iff
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {C : Finset V}
    (hCOutside : C ⊆ outsidePackingVertices S)
    {e : Finset V} :
    e ∈ G.spannedLabelledEdges S C ↔
      ∃ c ∈ C, G.Spans c e := by
  classical
  constructor
  · intro he
    exact (Finset.mem_filter.mp he).2
  · intro hSpanned
    obtain ⟨c, hcC, hcSpans⟩ := hSpanned
    change e ∈ (G.labelledPackingEdges S).filter
      (fun f ↦ ∃ z ∈ C, G.Spans z f)
    apply Finset.mem_filter.mpr
    refine ⟨G.mem_labelledPackingEdges_of_spans_outside hS ?_ hcSpans,
      ⟨c, hcC, hcSpans⟩⟩
    exact mem_outsidePackingVertices_iff.mp (hCOutside hcC)

end SimpleGraph
