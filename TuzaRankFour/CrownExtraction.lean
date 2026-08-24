import TuzaRankFour.DischargeCrown

/-!
# Extracting a fat-head crown from Hall deficiency

This file packages the matching supplied by `HallCore` into the exact crown
object used by the rank-four kernel reduction.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replacement triangles on distinct packing edges and distinct outside
vertices are edge-disjoint, even when their head edges belong to different
members of the original packing. -/
theorem card_inter_insert_triangleFamilyEdges_le_one
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    {e f : Finset V} (he : e ∈ triangleFamilyEdges S)
    (hf : f ∈ triangleFamilyEdges S) (hef : e ≠ f)
    {x y : V} (hxOutside : x ∉ triangleFamilyVertexSupport S)
    (hyOutside : y ∉ triangleFamilyVertexSupport S) (hxy : x ≠ y) :
    (insert x e ∩ insert y f).card ≤ 1 := by
  classical
  obtain ⟨t, htS, heSub, heCard⟩ := mem_triangleFamilyEdges_iff.mp he
  obtain ⟨u, huS, hfSub, hfCard⟩ := mem_triangleFamilyEdges_iff.mp hf
  by_cases htu : t = u
  · subst u
    exact card_inter_insert_edges_le_one_of_distinct_outside
      (Finset.mem_powersetCard.mpr ⟨heSub, heCard⟩)
      (Finset.mem_powersetCard.mpr ⟨hfSub, hfCard⟩)
      hef hxy
      (fun hxt ↦ hxOutside (Finset.mem_biUnion.mpr ⟨t, htS, hxt⟩))
      (fun hyt ↦ hyOutside (Finset.mem_biUnion.mpr ⟨t, htS, hyt⟩))
  · have hsub : insert x e ∩ insert y f ⊆ t ∩ u := by
      intro z hz
      simp only [Finset.mem_inter] at hz ⊢
      rcases Finset.mem_insert.mp hz.1 with rfl | hze
      · rcases Finset.mem_insert.mp hz.2 with hxy' | hxf
        · exact (hxy hxy').elim
        · exact (hxOutside
            (Finset.mem_biUnion.mpr ⟨u, huS, hfSub hxf⟩)).elim
      · rcases Finset.mem_insert.mp hz.2 with hyz | hzf
        · exact (hyOutside
            (Finset.mem_biUnion.mpr ⟨t, htS, heSub (hyz ▸ hze)⟩)).elim
        · exact ⟨heSub hze, hfSub hzf⟩
    exact (Finset.card_le_card hsub).trans (hS.2 htS huS htu)

/-- A Hall-deficient set of outside vertices gives a nonempty fat-head crown.
All crown fields are reconstructed from the deficient core and its matching. -/
theorem exists_nonempty_fatHeadCrown_of_deficient_spanners
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hTriangleSupport : G.triangleSupport = G)
    {I : Finset V} (hIOutside : I ⊆ outsidePackingVertices S)
    (hISpans : ∀ c ∈ I, ∃ e : Finset V, G.Spans c e)
    {A : Finset {c : V // c ∈ I}}
    (hA : (G.labelledSpannerNeighbors S I A).card < A.card) :
    ∃ K : G.FatHeadCrown, K.headEdges.Nonempty := by
  classical
  obtain ⟨C, hCdef, f, hfInjective, hfSpans⟩ :=
    G.exists_deficient_spanner_core_with_matching_back S I hA
  let H := G.labelledSpannerNeighbors S I C
  let C₀ : Finset V := FiniteRelation.values C
  let H₀ : Finset (Finset V) := FiniteRelation.values H
  let q := fun e : {e : {e : Finset V // e ∈ G.labelledPackingEdges S} // e ∈ H} ↦
    insert (f e).1.1 e.1.1
  let W : Finset (Finset V) := H.attach.image q
  have hC₀Outside : C₀ ⊆ outsidePackingVertices S := by
    intro c hc
    obtain ⟨c', hc'C, rfl⟩ := FiniteRelation.mem_values_iff.mp hc
    exact hIOutside c'.2
  have hH₀eq : H₀ = G.spannedLabelledEdges S C₀ := by
    ext e
    constructor
    · intro heH₀
      obtain ⟨e', he'H, he'eq⟩ :=
        FiniteRelation.mem_values_iff.mp heH₀
      subst e
      obtain ⟨c, hcC, hcSpans⟩ :=
        (G.mem_labelledSpannerNeighbors_iff).mp he'H
      rw [G.mem_spannedLabelledEdges_iff hS hC₀Outside]
      exact ⟨c.1,
        FiniteRelation.mem_values_iff.mpr ⟨c, hcC, rfl⟩,
        hcSpans⟩
    · intro heSpanned
      obtain ⟨c₀, hc₀C₀, hc₀Spans⟩ :=
        (G.mem_spannedLabelledEdges_iff hS hC₀Outside).mp heSpanned
      obtain ⟨c, hcC, hcEq⟩ :=
        FiniteRelation.mem_values_iff.mp hc₀C₀
      have heLabelled := G.mem_labelledPackingEdges_of_spans_outside hS
        (mem_outsidePackingVertices_iff.mp (hC₀Outside hc₀C₀)) hc₀Spans
      let e' : {e : Finset V // e ∈ G.labelledPackingEdges S} :=
        ⟨e, heLabelled⟩
      have he'H : e' ∈ H := by
        rw [G.mem_labelledSpannerNeighbors_iff]
        exact ⟨c, hcC, by simpa [hcEq] using hc₀Spans⟩
      exact FiniteRelation.mem_values_iff.mpr ⟨e', he'H, rfl⟩
  have hCnonempty : C.Nonempty := by
    apply Finset.card_pos.mp
    change H.card < C.card at hCdef
    omega
  have hC₀nonempty : C₀.Nonempty := by
    obtain ⟨c, hcC⟩ := hCnonempty
    exact ⟨c.1, FiniteRelation.mem_values_iff.mpr ⟨c, hcC, rfl⟩⟩
  have hqInjective : Function.Injective q := by
    intro e₁ e₂ hqEq
    apply hfInjective
    apply Subtype.ext
    apply Subtype.ext
    have hc₁mem : (f e₁).1.1 ∈ q e₁ := by simp [q]
    have hc₁mem₂ : (f e₁).1.1 ∈ q e₂ := by simpa [hqEq] using hc₁mem
    rcases Finset.mem_insert.mp hc₁mem₂ with hcEq | hcHead
    · exact hcEq
    · have he₂Family :=
        (G.mem_labelledPackingEdges_iff.mp e₂.1.2).1
      obtain ⟨t, htS, he₂Sub, _⟩ :=
        mem_triangleFamilyEdges_iff.mp he₂Family
      have hcOutside : (f e₁).1.1 ∉ triangleFamilyVertexSupport S :=
        mem_outsidePackingVertices_iff.mp
          (hIOutside (f e₁).1.2)
      exact (hcOutside
        (Finset.mem_biUnion.mpr ⟨t, htS, he₂Sub hcHead⟩)).elim
  have hWisPacking : G.IsTrianglePacking W := by
    constructor
    · intro t htW
      obtain ⟨e, _heAttach, rfl⟩ := Finset.mem_image.mp htW
      exact hfSpans e |>.2
    · intro t htW u huW htu
      obtain ⟨e, _heAttach, rfl⟩ := Finset.mem_image.mp htW
      obtain ⟨d, _hdAttach, rfl⟩ := Finset.mem_image.mp huW
      have hed : e ≠ d := by
        intro hed
        subst d
        exact htu rfl
      have hfd : f e ≠ f d := fun h ↦ hed (hfInjective h)
      exact G.card_inter_insert_triangleFamilyEdges_le_one hS.1
        (G.mem_labelledPackingEdges_iff.mp e.1.2).1
        (G.mem_labelledPackingEdges_iff.mp d.1.2).1
        (fun heq ↦ hed (Subtype.ext (Subtype.ext heq)))
        (mem_outsidePackingVertices_iff.mp (hIOutside (f e).1.2))
        (mem_outsidePackingVertices_iff.mp (hIOutside (f d).1.2))
        (fun hxy ↦ hfd (Subtype.ext (Subtype.ext hxy)))
  have hWcard : W.card = H₀.card := by
    change (H.attach.image q).card = H₀.card
    rw [Finset.card_image_of_injective _ hqInjective,
      Finset.card_attach]
    exact (FiniteRelation.card_values H).symm
  let K : G.FatHeadCrown := {
    crownVertices := C₀
    headEdges := H₀
    witnessPacking := W
    crown_independent := by
      intro u hu v hv huv
      exact G.isIndepSet_outsidePackingVertices hS hTriangleSupport
        (hC₀Outside hu) (hC₀Outside hv) huv
    head_iff_spanned := by
      intro e
      rw [hH₀eq, G.mem_spannedLabelledEdges_iff hS hC₀Outside]
    separated := by
      intro c hcC₀ x hxC₀ hxHead hcx
      exact hxHead (by
        rw [hH₀eq]
        exact G.neighbor_mem_spannedLabelledEdges_biUnion_of_outside
          hS hTriangleSupport hC₀Outside hcC₀ hcx)
    witness_isPacking := hWisPacking
    witness_card := hWcard
    witness_one_crown_vertex := by
      intro t htW
      obtain ⟨e, _heAttach, rfl⟩ := Finset.mem_image.mp htW
      have hcC₀ : (f e).1.1 ∈ C₀ :=
        FiniteRelation.mem_values_iff.mpr ⟨(f e).1, (f e).2, rfl⟩
      have heDisjoint : Disjoint e.1.1 C₀ := by
        rw [Finset.disjoint_left]
        intro z hze hzC₀
        have heFamily := (G.mem_labelledPackingEdges_iff.mp e.1.2).1
        obtain ⟨p, hpS, hep, _⟩ := mem_triangleFamilyEdges_iff.mp heFamily
        exact (mem_outsidePackingVertices_iff.mp (hC₀Outside hzC₀))
          (Finset.mem_biUnion.mpr ⟨p, hpS, hep hze⟩)
      have hinter : insert (f e).1.1 e.1.1 ∩ C₀ = {(f e).1.1} := by
        ext z
        constructor
        · intro hz
          have hzData := Finset.mem_inter.mp hz
          rcases Finset.mem_insert.mp hzData.1 with rfl | hze
          · simp
          · exact (Finset.disjoint_left.mp heDisjoint hze hzData.2).elim
        · intro hz
          have hzEq : z = (f e).1.1 := by simpa using hz
          subst z
          exact Finset.mem_inter.mpr ⟨by simp, hcC₀⟩
      rw [hinter]
      simp
    witness_one_head_edge := by
      intro t htW
      obtain ⟨e, _heAttach, rfl⟩ := Finset.mem_image.mp htW
      have heH₀ : e.1.1 ∈ H₀ :=
        FiniteRelation.mem_values_iff.mpr ⟨e.1, e.2, rfl⟩
      have hcOutside : (f e).1.1 ∉ triangleFamilyVertexSupport S :=
        mem_outsidePackingVertices_iff.mp (hIOutside (f e).1.2)
      have hfilter :
          H₀.filter (fun d ↦ d ⊆ insert (f e).1.1 e.1.1) = {e.1.1} := by
        ext d
        constructor
        · intro hd
          have hdData := Finset.mem_filter.mp hd
          have hdFamily :=
            (G.mem_labelledPackingEdges_iff.mp
              (by rw [hH₀eq] at hdData;
                  exact (Finset.mem_filter.mp hdData.1).1)).1
          obtain ⟨p, hpS, hdp, hdCard⟩ :=
            mem_triangleFamilyEdges_iff.mp hdFamily
          have hdSub : d ⊆ e.1.1 := by
            intro z hzd
            rcases Finset.mem_insert.mp (hdData.2 hzd) with hzc | hze
            · subst z
              exact (hcOutside
                (Finset.mem_biUnion.mpr ⟨p, hpS, hdp hzd⟩)).elim
            · exact hze
          have hde : d = e.1.1 :=
            Finset.eq_of_subset_of_card_le hdSub (by rw [hdCard, (hfSpans e).1])
          simpa [hde]
        · intro hd
          have hde : d = e.1.1 := by simpa using hd
          subst d
          exact Finset.mem_filter.mpr ⟨heH₀, by simp⟩
      rw [hfilter]
      simp
  }
  refine ⟨K, ?_⟩
  change H₀.Nonempty
  obtain ⟨c, hcC⟩ := hC₀nonempty
  have hHnonempty : H.Nonempty := by
    obtain ⟨e, hce⟩ := hISpans c
      (by obtain ⟨c', hc'C, hc'eq⟩ :=
            FiniteRelation.mem_values_iff.mp hcC
          simpa [← hc'eq] using c'.2)
    have heLabelled := G.mem_labelledPackingEdges_of_spans_outside hS
      (mem_outsidePackingVertices_iff.mp (hC₀Outside hcC)) hce
    let e' : {e : Finset V // e ∈ G.labelledPackingEdges S} :=
      ⟨e, heLabelled⟩
    obtain ⟨c', hc'C, hc'eq⟩ := FiniteRelation.mem_values_iff.mp hcC
    refine ⟨e', ?_⟩
    rw [G.mem_labelledSpannerNeighbors_iff]
    exact ⟨c', hc'C, by simpa [hc'eq] using hce⟩
  obtain ⟨e, heH⟩ := hHnonempty
  exact ⟨e.1, FiniteRelation.mem_values_iff.mpr ⟨e, heH, rfl⟩⟩

end SimpleGraph
