import TuzaRankFour.ComponentBound

/-!
# Classification for the twelve-vertex discharge

This file begins the second stage of the analytic discharge.  It records the
vertices incident with labelled packing edges and proves the basic
support-increasing exchange used to control the third vertex of a good packed
triangle.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices incident with labelled packing edges. -/
noncomputable def labelledPackingVertices (G : SimpleGraph V)
    (S : Finset (Finset V)) : Finset V :=
  triangleFamilyVertexSupport (G.labelledPackingEdges S)

@[simp]
theorem mem_labelledPackingVertices_iff
    (G : SimpleGraph V) {S : Finset (Finset V)} {v : V} :
    v ∈ G.labelledPackingVertices S ↔
      ∃ e ∈ G.labelledPackingEdges S, v ∈ e := by
  classical
  simp [labelledPackingVertices, triangleFamilyVertexSupport]

/-- Replacing a packed triangle by a triangle on one of its edges and a new
outside vertex improves packing support whenever the omitted packed vertex is
preserved by a retained packing member. -/
theorem false_of_spanned_edge_and_retained_omitted_vertex
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t e : Finset V} (htS : t ∈ S)
    (he : e ∈ t.powersetCard 2)
    {x : V} (hxOutside : x ∉ triangleFamilyVertexSupport S)
    (hxeTriangle : insert x e ∈ G.triangles)
    {w : V} (hwt : w ∈ t) (hwe : w ∉ e)
    {p : Finset V} (hp : p ∈ S.erase t) (hwp : w ∈ p) : False := by
  classical
  let R := S.erase t
  let face := insert x e
  let P := insert face R
  have heData := Finset.mem_powersetCard.mp he
  have htTriangle : t ∈ G.triangles := hS.1.1 htS
  have htCard : t.card = 3 := G.card_eq_three_of_mem_triangles htTriangle
  have hEraseCard : (t.erase w).card = 2 := by
    rw [Finset.card_erase_of_mem hwt, htCard]
  have heSubErase : e ⊆ t.erase w := by
    intro v hve
    exact Finset.mem_erase.mpr ⟨fun hvw ↦ hwe (hvw ▸ hve), heData.1 hve⟩
  have heErase : e = t.erase w :=
    Finset.eq_of_subset_of_card_le heSubErase (by omega)
  have hxNotT : x ∉ t := by
    intro hxt
    exact hxOutside (Finset.mem_biUnion.mpr ⟨t, htS, hxt⟩)
  have hRpacking : G.IsTrianglePacking R :=
    hS.1.mono_family G (Finset.erase_subset _ _)
  have hcompat : ∀ ⦃q⦄, q ∈ R → (q ∩ face).card ≤ 1 := by
    intro q hq
    have hqS : q ∈ S := Finset.mem_of_mem_erase hq
    have hqt : q ≠ t := Finset.ne_of_mem_erase hq
    have hxq : x ∉ q := by
      intro hxq
      exact hxOutside (Finset.mem_biUnion.mpr ⟨q, hqS, hxq⟩)
    have hsub : q ∩ face ⊆ q ∩ t := by
      intro v hv
      simp only [Finset.mem_inter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      rcases Finset.mem_insert.mp hv.2 with rfl | hve
      · exact (hxq hv.1).elim
      · exact heData.1 hve
    exact (Finset.card_le_card hsub).trans (hS.1.2 hqS htS hqt)
  have hPpacking : G.IsTrianglePacking P :=
    G.isTrianglePacking_insert hRpacking hxeTriangle hcompat
  have hxFace : x ∈ face := by simp [face]
  have hfaceNotR : face ∉ R := by
    intro hfaceR
    have hfaceS : face ∈ S := Finset.mem_of_mem_erase hfaceR
    exact hxOutside (Finset.mem_biUnion.mpr ⟨face, hfaceS, hxFace⟩)
  have hcardP : P.card = S.card := by
    change (insert face R).card = S.card
    rw [Finset.card_insert_of_notMem hfaceNotR]
    change (S.erase t).card + 1 = S.card
    rw [Finset.card_erase_of_mem htS]
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨t, htS⟩
    omega
  have hsupportSubset : triangleFamilyVertexSupport S ⊆
      triangleFamilyVertexSupport P := by
    intro v hv
    obtain ⟨q, hqS, hvq⟩ := Finset.mem_biUnion.mp hv
    by_cases hqt : q = t
    · subst q
      by_cases hvw : v = w
      · subst v
        exact Finset.mem_biUnion.mpr
          ⟨p, by simp [P, R, hp], hwp⟩
      · have hve : v ∈ e := by
          rw [heErase]
          exact Finset.mem_erase.mpr ⟨hvw, hvq⟩
        exact Finset.mem_biUnion.mpr
          ⟨face, by simp [P], Finset.mem_insert_of_mem hve⟩
    · have hqR : q ∈ R := by simp [R, hqS, hqt]
      exact Finset.mem_biUnion.mpr ⟨q, by simp [P, hqR], hvq⟩
  have hxSupportP : x ∈ triangleFamilyVertexSupport P :=
    Finset.mem_biUnion.mpr ⟨face, by simp [P], hxFace⟩
  have hsupportNe : triangleFamilyVertexSupport S ≠
      triangleFamilyVertexSupport P := by
    intro hEq
    exact hxOutside (hEq ▸ hxSupportP)
  have hsupportLt : (triangleFamilyVertexSupport S).card <
      (triangleFamilyVertexSupport P).card :=
    Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsupportSubset, hsupportNe⟩)
  have hmax := hS.2.2 hPpacking (hcardP.trans hS.2.1)
  omega

/-- The vertex of a good packed triangle opposite its labelled edge is not
incident with any labelled packing edge. -/
theorem opposite_vertex_not_mem_labelledPackingVertices
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (hNoK4 : ∀ Q : Finset V, ¬G.IsTriangleIsolatedK4 Q)
    {t e : Finset V} (htS : t ∈ S)
    (heLabelled : e ∈ G.labelledEdgesInTriangle S t)
    {w : V} (hwt : w ∈ t) (hwe : w ∉ e) :
    w ∉ G.labelledPackingVertices S := by
  classical
  intro hwLabelled
  obtain ⟨f, hfLabelled, hwf⟩ :=
    (G.mem_labelledPackingVertices_iff).mp hwLabelled
  have hfFamily := (G.mem_labelledPackingEdges_iff.mp hfLabelled).1
  obtain ⟨p, hpS, hfSub, hfCard⟩ :=
    mem_triangleFamilyEdges_iff.mp hfFamily
  have hfPacked : f ∈ p.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hfSub, hfCard⟩
  have hpt : p ≠ t := by
    intro hpt
    subst p
    have hfSlice : f ∈ G.labelledEdgesInTriangle S t :=
      Finset.mem_inter.mpr ⟨hfPacked, hfLabelled⟩
    have hle := G.card_labelled_edges_in_packed_triangle_le_one
      hS hNoK4 htS
    have hef := (Finset.card_le_one_iff.mp hle) heLabelled hfSlice
    apply hwe
    rw [hef]
    exact hwf
  have hpErase : p ∈ S.erase t := Finset.mem_erase.mpr ⟨hpt, hpS⟩
  obtain ⟨x, hxSpans⟩ :=
    (G.mem_labelledPackingEdges_iff.mp
      (Finset.mem_inter.mp heLabelled).2).2
  rw [G.mem_packingEdgeSpanners_iff] at hxSpans
  exact G.false_of_spanned_edge_and_retained_omitted_vertex
    hS htS (Finset.mem_inter.mp heLabelled).1 hxSpans.1 hxSpans.2
      hwt hwe hpErase (hfSub hwf)

/-- A triangle remains after deleting the labelled packing edges when none of
its three edges is labelled. -/
def TriangleAvoidsPackingLabels (G : SimpleGraph V)
    (S : Finset (Finset V)) (r : Finset V) : Prop :=
  r ∈ G.triangles ∧
    Disjoint (r.powersetCard 2) (G.labelledPackingEdges S)

/-- A good packed triangle is excellent when neither of its unlabelled edges
is contained in a triangle surviving deletion of all labelled edges. -/
def IsExcellentPackingTriangle (G : SimpleGraph V)
    (S : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.goodPackingTriangles S ∧
    ∀ ⦃e : Finset V⦄, e ∈ t.powersetCard 2 →
      e ∉ G.labelledPackingEdges S →
      ∀ ⦃r : Finset V⦄, G.TriangleAvoidsPackingLabels S r →
        ¬e ⊆ r

/-- Excellent members of the packing. -/
noncomputable def excellentPackingTriangles (G : SimpleGraph V)
    (S : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact (G.goodPackingTriangles S).filter
    (G.IsExcellentPackingTriangle S)

/-- Good but nonexcellent members of the packing. -/
noncomputable def prettyGoodPackingTriangles (G : SimpleGraph V)
    (S : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact (G.goodPackingTriangles S).filter
    (fun t ↦ ¬G.IsExcellentPackingTriangle S t)

@[simp]
theorem mem_excellentPackingTriangles_iff
    (G : SimpleGraph V) {S : Finset (Finset V)} {t : Finset V} :
    t ∈ G.excellentPackingTriangles S ↔
      G.IsExcellentPackingTriangle S t := by
  classical
  simp [excellentPackingTriangles, IsExcellentPackingTriangle]

@[simp]
theorem mem_prettyGoodPackingTriangles_iff
    (G : SimpleGraph V) {S : Finset (Finset V)} {t : Finset V} :
    t ∈ G.prettyGoodPackingTriangles S ↔
      t ∈ G.goodPackingTriangles S ∧
        ¬G.IsExcellentPackingTriangle S t := by
  classical
  simp [prettyGoodPackingTriangles]

/-- Excellent and pretty-good triangles partition the good triangles. -/
theorem excellent_union_prettyGood_eq_good
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    G.excellentPackingTriangles S ∪
      G.prettyGoodPackingTriangles S = G.goodPackingTriangles S := by
  classical
  ext t
  simp only [Finset.mem_union, G.mem_excellentPackingTriangles_iff,
    G.mem_prettyGoodPackingTriangles_iff]
  constructor
  · rintro (ht | ⟨ht, _⟩)
    · exact ht.1
    · exact ht
  · intro ht
    by_cases hExcellent : G.IsExcellentPackingTriangle S t
    · exact Or.inl hExcellent
    · exact Or.inr ⟨ht, hExcellent⟩

theorem disjoint_excellent_prettyGood
    (G : SimpleGraph V) (S : Finset (Finset V)) :
    Disjoint (G.excellentPackingTriangles S)
      (G.prettyGoodPackingTriangles S) := by
  classical
  rw [Finset.disjoint_left]
  intro t htExcellent htPretty
  rw [G.mem_excellentPackingTriangles_iff] at htExcellent
  rw [G.mem_prettyGoodPackingTriangles_iff] at htPretty
  exact htPretty.2 htExcellent

/-- Vertices private to the excellent class after excluding labelled-edge
vertices and vertices also used by pretty-good or bad packed triangles. -/
noncomputable def excellentResidualVertices (G : SimpleGraph V)
    (S : Finset (Finset V)) : Finset V :=
  triangleFamilyVertexSupport (G.excellentPackingTriangles S) \
    (G.labelledPackingVertices S ∪
      triangleFamilyVertexSupport (G.prettyGoodPackingTriangles S) ∪
      triangleFamilyVertexSupport (G.badPackingTriangles S))

/-- Unlabelled-edge vertices belonging to pretty-good packed triangles. -/
noncomputable def prettyGoodResidualVertices (G : SimpleGraph V)
    (S : Finset (Finset V)) : Finset V :=
  triangleFamilyVertexSupport (G.prettyGoodPackingTriangles S) \
    G.labelledPackingVertices S

@[simp]
theorem mem_excellentResidualVertices_iff
    (G : SimpleGraph V) {S : Finset (Finset V)} {v : V} :
    v ∈ G.excellentResidualVertices S ↔
      v ∈ triangleFamilyVertexSupport (G.excellentPackingTriangles S) ∧
      v ∉ G.labelledPackingVertices S ∧
      v ∉ triangleFamilyVertexSupport (G.prettyGoodPackingTriangles S) ∧
      v ∉ triangleFamilyVertexSupport (G.badPackingTriangles S) := by
  classical
  simp [excellentResidualVertices, and_assoc]

@[simp]
theorem mem_prettyGoodResidualVertices_iff
    (G : SimpleGraph V) {S : Finset (Finset V)} {v : V} :
    v ∈ G.prettyGoodResidualVertices S ↔
      v ∈ triangleFamilyVertexSupport (G.prettyGoodPackingTriangles S) ∧
      v ∉ G.labelledPackingVertices S := by
  classical
  simp [prettyGoodResidualVertices]

/-- Good packed triangles lying in one packing-intersection component. -/
noncomputable def goodTrianglesInComponent (G : SimpleGraph V)
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    Finset (Finset V) :=
  packingComponentTriangles S C ∩ G.goodPackingTriangles S

/-- Bad packed triangles lying in one packing-intersection component. -/
noncomputable def badTrianglesInComponent (G : SimpleGraph V)
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    Finset (Finset V) :=
  packingComponentTriangles S C ∩ G.badPackingTriangles S

theorem goodTrianglesInComponent_union_badTrianglesInComponent
    (G : SimpleGraph V) (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    G.goodTrianglesInComponent S C ∪
      G.badTrianglesInComponent S C = packingComponentTriangles S C := by
  classical
  ext t
  simp only [goodTrianglesInComponent, badTrianglesInComponent,
    Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  · intro ht
    have htS := packingComponentTriangles_subset C ht
    have htPartition :
        t ∈ G.goodPackingTriangles S ∨ t ∈ G.badPackingTriangles S := by
      have := congrArg (fun Q : Finset (Finset V) ↦ t ∈ Q)
        (G.good_union_bad_eq S)
      simpa using this.mpr htS
    exact htPartition.elim (fun h ↦ Or.inl ⟨ht, h⟩)
      (fun h ↦ Or.inr ⟨ht, h⟩)

theorem disjoint_goodTrianglesInComponent_badTrianglesInComponent
    (G : SimpleGraph V) (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    Disjoint (G.goodTrianglesInComponent S C)
      (G.badTrianglesInComponent S C) := by
  classical
  exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
    (G.disjoint_good_bad S)

/-- The charge placed on component vertices after the first move is
`2 * good + 3 * bad = 2 * total + bad`. -/
theorem component_vertex_charge_count
    (G : SimpleGraph V) (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    2 * (G.goodTrianglesInComponent S C).card +
        3 * (G.badTrianglesInComponent S C).card =
      2 * (packingComponentTriangles S C).card +
        (G.badTrianglesInComponent S C).card := by
  have hcard := congrArg Finset.card
    (G.goodTrianglesInComponent_union_badTrianglesInComponent S C)
  rw [Finset.card_union_of_disjoint
    (G.disjoint_goodTrianglesInComponent_badTrianglesInComponent S C)] at hcard
  omega

/-- Independently of whether a component contains a bad triangle, its first
round of vertex charge is short of its support size by at most one. -/
theorem card_componentSupport_le_vertexCharge_add_one
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    (packingComponentVertexSupport S C).card ≤
      (2 * (packingComponentTriangles S C).card +
        (G.badTrianglesInComponent S C).card) + 1 := by
  have hbound := card_packingComponentVertexSupport_le hS C
  omega

/-- A component containing a bad triangle has enough first-round charge for
all of its support vertices. -/
theorem card_componentSupport_le_vertexCharge_of_bad_nonempty
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hBad : (G.badTrianglesInComponent S C).Nonempty) :
    (packingComponentVertexSupport S C).card ≤
      2 * (packingComponentTriangles S C).card +
        (G.badTrianglesInComponent S C).card := by
  have hbound := card_packingComponentVertexSupport_le hS C
  have hpositive := Finset.card_pos.mpr hBad
  omega

end SimpleGraph
