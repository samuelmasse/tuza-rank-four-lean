import TuzaRankFour.TransferLedger
import TuzaRankFour.Exchange

/-!
# Componentwise transfer configuration

This file reconstructs the local configuration forced by a pretty-good
packing triangle.  It is the geometric input to the two-edge component
transfer.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A packed triangle sharing a vertex with a member of a packing component
belongs to that same component. -/
theorem mem_packingComponentTriangles_of_inter_nonempty
    {S : Finset (Finset V)}
    {C : (packingIntersectionGraph S).ConnectedComponent}
    {s t : Finset V} (hsC : s ∈ packingComponentTriangles S C)
    (htS : t ∈ S) (hst : s ≠ t) (hinter : (s ∩ t).Nonempty) :
    t ∈ packingComponentTriangles S C := by
  classical
  obtain ⟨q, rfl⟩ := mem_packingComponentTriangles_iff.mp hsC
  let r : {p : Finset V // p ∈ S} := ⟨t, htS⟩
  have hqr : q.1 ≠ r := by
    intro hEq
    apply hst
    exact congrArg Subtype.val hEq
  have hadj : (packingIntersectionGraph S).Adj q.1 r :=
    packingIntersectionGraph_adj_iff.mpr ⟨hqr, hinter⟩
  have hmk :
      (packingIntersectionGraph S).connectedComponentMk q.1 =
        (packingIntersectionGraph S).connectedComponentMk r :=
    ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)
  have hqC :
      (packingIntersectionGraph S).connectedComponentMk q.1 = C :=
    (C.mem_supp_iff q.1).mp q.2
  have hrC :
      (packingIntersectionGraph S).connectedComponentMk r = C :=
    hmk.symm.trans hqC
  have hrSupp : r ∈ C.supp := (C.mem_supp_iff r).mpr hrC
  exact mem_packingComponentTriangles_iff.mpr ⟨⟨r, hrSupp⟩, rfl⟩

/-- A packing component is all-good when each of its packed triangles owns a
labelled edge. -/
def IsAllGoodPackingComponent (G : SimpleGraph V)
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) : Prop :=
  packingComponentTriangles S C ⊆ G.goodPackingTriangles S

/-- The local data consumed by one componentwise two-edge transfer. -/
structure ComponentTransferWitness (G : SimpleGraph V)
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (z : V) where
  firstTriangle : Finset V
  secondTriangle : Finset V
  firstEdge : Finset V
  secondEdge : Finset V
  spanner : V
  first_mem_component : firstTriangle ∈ packingComponentTriangles S C
  second_mem_component : secondTriangle ∈ packingComponentTriangles S C
  first_prettyGood : firstTriangle ∈ G.prettyGoodPackingTriangles S
  second_prettyGood : secondTriangle ∈ G.prettyGoodPackingTriangles S
  target_mem_first : z ∈ firstTriangle
  first_subset : firstEdge ⊆ firstTriangle
  second_subset : secondEdge ⊆ secondTriangle
  first_labelled : firstEdge ∈ G.labelledPackingEdges S
  second_labelled : secondEdge ∈ G.labelledPackingEdges S
  edges_ne : firstEdge ≠ secondEdge
  first_spanners : G.packingEdgeSpanners S firstEdge = {spanner}
  second_spanners : G.packingEdgeSpanners S secondEdge = {spanner}

omit [Fintype V] in
/-- Two distinct two-subsets of a three-set meet in exactly one vertex. -/
theorem card_inter_eq_one_of_distinct_powersetCard_two
    {t e f : Finset V} (htCard : t.card = 3)
    (he : e ∈ t.powersetCard 2) (hf : f ∈ t.powersetCard 2)
    (hef : e ≠ f) : (e ∩ f).card = 1 := by
  classical
  have heData := Finset.mem_powersetCard.mp he
  have hfData := Finset.mem_powersetCard.mp hf
  have hupper := card_inter_le_one_of_card_eq_two
    heData.2 hfData.2 hef
  have hunion := union_eq_of_mem_powersetCard_two_of_card_three
    htCard he hf hef
  have hcardUnion : (e ∪ f).card = 3 := by rw [hunion, htCard]
  rw [Finset.card_union] at hcardUnion
  omega

omit [Fintype V] in
/-- A two-subset of a three-set has a unique complementary vertex. -/
theorem exists_complement_vertex_of_powersetCard_two
    {t e : Finset V} (htCard : t.card = 3)
    (he : e ∈ t.powersetCard 2) :
    ∃ w, w ∉ e ∧ t = insert w e := by
  classical
  have heData := Finset.mem_powersetCard.mp he
  have hdiffCard : (t \ e).card = 1 := by
    rw [Finset.card_sdiff_of_subset heData.1, htCard, heData.2]
  obtain ⟨w, hwEq⟩ := Finset.card_eq_one.mp hdiffCard
  have hwDiff : w ∈ t \ e := by simp [hwEq]
  refine ⟨w, (Finset.mem_sdiff.mp hwDiff).2, ?_⟩
  apply Finset.Subset.antisymm
  · intro z hzt
    by_cases hze : z ∈ e
    · exact Finset.mem_insert_of_mem hze
    · have hzDiff : z ∈ t \ e := Finset.mem_sdiff.mpr ⟨hzt, hze⟩
      have : z = w := by simpa [hwEq] using hzDiff
      simpa [this]
  · exact Finset.insert_subset (Finset.mem_sdiff.mp hwDiff).1 heData.1

omit [Fintype V] in
/-- The two-subsets of a three-element set are its three displayed pairs. -/
theorem mem_powersetCard_two_triple_iff
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {e : Finset V} :
    e ∈ ({a, b, c} : Finset V).powersetCard 2 ↔
      e = {a, b} ∨ e = {a, c} ∨ e = {b, c} := by
  classical
  constructor
  · intro he
    have heData := Finset.mem_powersetCard.mp he
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp heData.2
    have hp := heData.1 (by simp : p ∈ ({p, q} : Finset V))
    have hq := heData.1 (by simp : q ∈ ({p, q} : Finset V))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl <;>
      simp_all [Finset.pair_comm]
  · rintro (rfl | rfl | rfl)
    · exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [hab]⟩
    · exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [hac]⟩
    · exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [hbc]⟩

/-- A pretty-good triangle supplies labelled and unlabelled incident edges
`uv` and `uw`, with `uw` lying in a triangle `uwx` that avoids every labelled
packing edge. -/
theorem exists_prettyGood_transfer_configuration
    (G : SimpleGraph V) {S : Finset (Finset V)} {t : Finset V}
    (hS : G.IsTrianglePacking S)
    (htPretty : t ∈ G.prettyGoodPackingTriangles S) :
    ∃ u v w x : V,
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      x ≠ u ∧ x ≠ v ∧ x ≠ w ∧
      t = {u, v, w} ∧
      {u, v} ∈ G.labelledPackingEdges S ∧
      ∃ r : Finset V,
        r = {u, w, x} ∧ G.TriangleAvoidsPackingLabels S r := by
  classical
  have htGood := (G.mem_prettyGoodPackingTriangles_iff.mp htPretty).1
  have htS := (G.mem_goodPackingTriangles_iff.mp htGood).1
  have htCard : t.card = 3 := G.card_eq_three_of_mem_triangles (hS.1 htS)
  obtain ⟨l, hlSlice⟩ := (G.mem_goodPackingTriangles_iff.mp htGood).2
  have hlData := Finset.mem_inter.mp hlSlice
  obtain ⟨e, heT, heNotLabelled, r, hrAvoids, heSubR⟩ :=
    G.exists_avoiding_triangle_on_unlabelled_edge_of_prettyGood htPretty
  have hel : e ≠ l := fun hel ↦ heNotLabelled (hel ▸ hlData.2)
  have hinterCard : (e ∩ l).card = 1 :=
    card_inter_eq_one_of_distinct_powersetCard_two htCard heT hlData.1 hel
  obtain ⟨u, huInterEq⟩ := Finset.card_eq_one.mp hinterCard
  have huInter : u ∈ e ∩ l := by simp [huInterEq]
  have hue : u ∈ e := (Finset.mem_inter.mp huInter).1
  have hul : u ∈ l := (Finset.mem_inter.mp huInter).2
  have hlCard : l.card = 2 := (Finset.mem_powersetCard.mp hlData.1).2
  have heCard : e.card = 2 := (Finset.mem_powersetCard.mp heT).2
  have hlEraseCard : (l.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hul, hlCard]
  have heEraseCard : (e.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hue, heCard]
  obtain ⟨v, hvEraseEq⟩ := Finset.card_eq_one.mp hlEraseCard
  obtain ⟨w, hwEraseEq⟩ := Finset.card_eq_one.mp heEraseCard
  have hvl : v ∈ l := by
    have : v ∈ l.erase u := by simp [hvEraseEq]
    exact Finset.mem_of_mem_erase this
  have hwE : w ∈ e := by
    have : w ∈ e.erase u := by simp [hwEraseEq]
    exact Finset.mem_of_mem_erase this
  have huv : u ≠ v := by
    have : v ∈ l.erase u := by simp [hvEraseEq]
    exact (Finset.mem_erase.mp this).1.symm
  have huw : u ≠ w := by
    have : w ∈ e.erase u := by simp [hwEraseEq]
    exact (Finset.mem_erase.mp this).1.symm
  have hlEq : l = {u, v} := by
    rw [← Finset.insert_erase hul, hvEraseEq]
  have heEq : e = {u, w} := by
    rw [← Finset.insert_erase hue, hwEraseEq]
  have hvw : v ≠ w := by
    intro hvw
    subst w
    apply hel
    rw [hlEq, heEq]
  have htEq : t = {u, v, w} := by
    have hunion := union_eq_of_mem_powersetCard_two_of_card_three
      htCard heT hlData.1 hel
    rw [← hunion, hlEq, heEq]
    ext z
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hrCard : r.card = 3 := G.card_eq_three_of_mem_triangles hrAvoids.1
  have heR : e ∈ r.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨heSubR, heCard⟩
  obtain ⟨x, hxNotE, hrEqInsert⟩ :=
    exists_complement_vertex_of_powersetCard_two hrCard heR
  have hxu : x ≠ u := fun h ↦ hxNotE (h ▸ hue)
  have hxw : x ≠ w := fun h ↦ hxNotE (h ▸ hwE)
  have hrEq : r = {u, w, x} := by
    rw [hrEqInsert, heEq]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hxv : x ≠ v := by
    intro hxv
    have huvR : ({u, v} : Finset V) ∈ r.powersetCard 2 := by
      rw [hrEq]
      subst x
      exact (mem_powersetCard_two_triple_iff huw huv hvw.symm).mpr
        (Or.inr (Or.inl rfl))
    exact (Finset.disjoint_left.mp hrAvoids.2 huvR)
      (by simpa [hlEq] using hlData.2)
  exact ⟨u, v, w, x, huv, huw, hvw, hxu, hxv, hxw, htEq,
    by simpa [hlEq] using hlData.2, r, hrEq, hrAvoids⟩

/-- If the two edges of the avoiding triangle other than its packed base are
not packing edges, then that triangle is compatible with every retained
packing member. -/
theorem card_inter_prettyGood_witness_le_one_of_other_edges_not_packing
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    {t p r : Finset V} (htS : t ∈ S) (hp : p ∈ S.erase t)
    {u v w x : V}
    (huw : u ≠ w)
    (hxu : x ≠ u) (hxw : x ≠ w)
    (htEq : t = {u, v, w}) (hrEq : r = {u, w, x})
    (huxNot : ({u, x} : Finset V) ∉ triangleFamilyEdges S)
    (hwxNot : ({w, x} : Finset V) ∉ triangleFamilyEdges S) :
    (p ∩ r).card ≤ 1 := by
  classical
  by_contra hsmall
  have htwo : 2 ≤ (p ∩ r).card := by omega
  obtain ⟨f, hfSub, hfCard⟩ :=
    Finset.exists_subset_card_eq (s := p ∩ r) (n := 2) htwo
  have hfP : f ∈ p.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_left, hfCard⟩
  have hfR : f ∈ r.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_right, hfCard⟩
  have hpS : p ∈ S := Finset.mem_of_mem_erase hp
  have hfFamily : f ∈ triangleFamilyEdges S := by
    rw [mem_triangleFamilyEdges_iff]
    exact ⟨p, hpS, (Finset.mem_powersetCard.mp hfP).1, hfCard⟩
  rw [hrEq] at hfR
  rcases (mem_powersetCard_two_triple_iff
      huw hxu.symm hxw.symm).mp hfR with hfEq | hfEq | hfEq
  · have huwT : ({u, w} : Finset V) ∈ t.powersetCard 2 := by
      rw [htEq]
      exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [huw]⟩
    have hpEq := G.eq_of_mem_powersetCard_of_isTrianglePacking
      hS hpS htS hfP (hfEq ▸ huwT)
    exact (Finset.ne_of_mem_erase hp) hpEq
  · exact huxNot (hfEq ▸ hfFamily)
  · exact hwxNot (hfEq ▸ hfFamily)

/-- In the pretty-good witness configuration, maximality forces the edge
through the labelled-edge endpoint into the packing and excludes the edge
through the residual vertex. -/
theorem first_other_edge_mem_and_second_not_mem_of_prettyGood_configuration
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t r : Finset V} (htS : t ∈ S)
    {u v w x : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w)
    (htEq : t = {u, v, w})
    (huvLabelled : ({u, v} : Finset V) ∈ G.labelledPackingEdges S)
    (hrEq : r = {u, w, x})
    (hrAvoids : G.TriangleAvoidsPackingLabels S r) :
    ({u, x} : Finset V) ∈ triangleFamilyEdges S ∧
      ({w, x} : Finset V) ∉ triangleFamilyEdges S := by
  classical
  have huvT : ({u, v} : Finset V) ∈ t.powersetCard 2 := by
    rw [htEq]
    exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [huv]⟩
  have huwT : ({u, w} : Finset V) ∈ t.powersetCard 2 := by
    rw [htEq]
    exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [huw]⟩
  have huwFamily : ({u, w} : Finset V) ∈ triangleFamilyEdges S := by
    rw [mem_triangleFamilyEdges_iff]
    exact ⟨t, htS, (Finset.mem_powersetCard.mp huwT).1,
      (Finset.mem_powersetCard.mp huwT).2⟩
  obtain ⟨q, hqSpans⟩ :=
    (G.mem_labelledPackingEdges_iff.mp huvLabelled).2
  rw [G.mem_packingEdgeSpanners_iff] at hqSpans
  have hqNotT : q ∉ t := by
    intro hqt
    exact hqSpans.1 (Finset.mem_biUnion.mpr ⟨t, htS, hqt⟩)
  have hqu : q ≠ u := by
    intro h
    apply hqNotT
    rw [htEq, h]
    simp
  have hqv : q ≠ v := by
    intro h
    apply hqNotT
    rw [htEq, h]
    simp
  have hqw : q ≠ w := by
    intro h
    apply hqNotT
    rw [htEq, h]
    simp
  have hqx : q ≠ x := by
    intro h
    subst x
    have hqUwTriangle : insert q ({u, w} : Finset V) ∈ G.triangles := by
      have hset : insert q ({u, w} : Finset V) = r := by
        rw [hrEq]
        ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        aesop
      simpa [hset] using hrAvoids.1
    have hqUwSpanner : q ∈ G.packingEdgeSpanners S {u, w} := by
      rw [G.mem_packingEdgeSpanners_iff]
      exact ⟨hqSpans.1, hqUwTriangle⟩
    have huwLabelled : ({u, w} : Finset V) ∈
        G.labelledPackingEdges S := by
      rw [G.mem_labelledPackingEdges_iff]
      exact ⟨huwFamily, ⟨q, hqUwSpanner⟩⟩
    have huwR : ({u, w} : Finset V) ∈ r.powersetCard 2 := by
      rw [hrEq]
      exact (mem_powersetCard_two_triple_iff huw hqu.symm hqw.symm).mpr
        (Or.inl rfl)
    exact (Finset.disjoint_left.mp hrAvoids.2 huwR) huwLabelled
  have hwxNot : ({w, x} : Finset V) ∉ triangleFamilyEdges S := by
    intro hwxFamily
    obtain ⟨p, hpS, hwxSub, hwxCard⟩ :=
      mem_triangleFamilyEdges_iff.mp hwxFamily
    have hxp : x ∈ p := hwxSub (by simp)
    have hwp : w ∈ p := hwxSub (by simp)
    have hpNeT : p ≠ t := by
      intro hpEq
      subst p
      have hxt : x ∈ ({u, v, w} : Finset V) := by simpa [htEq] using hxp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
      rcases hxt with hxu' | hxv' | hxw'
      · exact hxu hxu'
      · exact hxv hxv'
      · exact hxw hxw'
    have hpErase : p ∈ S.erase t := Finset.mem_erase.mpr ⟨hpNeT, hpS⟩
    exact G.false_of_spanned_edge_and_retained_omitted_vertex
      hS htS huvT hqSpans.1 hqSpans.2
      (by rw [htEq]; simp)
      (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨huw.symm, hvw.symm⟩)
      hpErase hwp
  have huxMem : ({u, x} : Finset V) ∈ triangleFamilyEdges S := by
    by_contra huxNot
    have hab : (insert q ({u, v} : Finset V) ∩ r).card ≤ 1 := by
      have hdis : Disjoint ({u, v} : Finset V) {w, x} := by
        rw [Finset.disjoint_left]
        intro z hzLeft hzRight
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft hzRight
        rcases hzLeft with rfl | rfl
        · rcases hzRight with huw' | hux'
          · exact huw huw'
          · exact hxu hux'.symm
        · rcases hzRight with hvw' | hvx'
          · exact hvw hvw'
          · exact hxv hvx'.symm
      have hinterEmpty :
          ({u, v} : Finset V) ∩ {w, x} = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp hdis
      rw [hrEq]
      simp [hqu, hqw, hqx, hinterEmpty]
    have haR : ∀ ⦃p⦄, p ∈ S.erase t →
        (p ∩ insert q ({u, v} : Finset V)).card ≤ 1 := by
      intro p hp
      exact G.card_inter_insert_edge_le_one_of_outside hS.1
        (Finset.mem_of_mem_erase hp) htS (Finset.ne_of_mem_erase hp)
        (Finset.mem_powersetCard.mp huvT).1 hqSpans.1
    have hrR : ∀ ⦃p⦄, p ∈ S.erase t → (p ∩ r).card ≤ 1 := by
      intro p hp
      exact G.card_inter_prettyGood_witness_le_one_of_other_edges_not_packing
        hS.1 htS hp huw hxu hxw htEq hrEq huxNot hwxNot
    exact G.false_of_two_for_one_exchange hS htS
      hqSpans.2 hrAvoids.1 hab haR hrR
  exact ⟨huxMem, hwxNot⟩

/-- The second packed triangle in the transfer configuration is itself
pretty-good, and its labelled edge is the pair joining the common endpoint
to its complementary vertex. -/
theorem second_triangle_labelled_edge_of_prettyGood_configuration
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t t₂ r : Finset V} (htS : t ∈ S) (ht₂S : t₂ ∈ S)
    (htt₂ : t ≠ t₂)
    {u v w x y : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w)
    (hyu : y ≠ u) (hyx : y ≠ x)
    (htEq : t = {u, v, w}) (ht₂Eq : t₂ = {u, x, y})
    (huvLabelled : ({u, v} : Finset V) ∈ G.labelledPackingEdges S)
    (hrEq : r = {u, w, x})
    (hrAvoids : G.TriangleAvoidsPackingLabels S r)
    (ht₂Good : t₂ ∈ G.goodPackingTriangles S) :
    ({u, y} : Finset V) ∈ G.labelledPackingEdges S ∧
      t₂ ∈ G.prettyGoodPackingTriangles S := by
  classical
  have huxT₂ : ({u, x} : Finset V) ∈ t₂.powersetCard 2 := by
    rw [ht₂Eq]
    exact Finset.mem_powersetCard.mpr ⟨by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop, by simp [hxu.symm]⟩
  have huxR : ({u, x} : Finset V) ∈ r.powersetCard 2 := by
    rw [hrEq]
    exact (mem_powersetCard_two_triple_iff huw hxu.symm hxw.symm).mpr
      (Or.inr (Or.inl rfl))
  have huxNotLabelled : ({u, x} : Finset V) ∉
      G.labelledPackingEdges S :=
    Finset.disjoint_left.mp hrAvoids.2 huxR
  obtain ⟨l, hlSlice⟩ := (G.mem_goodPackingTriangles_iff.mp ht₂Good).2
  have hlData := Finset.mem_inter.mp hlSlice
  have hlNeUx : l ≠ ({u, x} : Finset V) := by
    intro hlEq
    exact huxNotLabelled (hlEq ▸ hlData.2)
  have hlNeXy : l ≠ ({x, y} : Finset V) := by
    intro hlEq
    have hxyLabelled : ({x, y} : Finset V) ∈
        G.labelledPackingEdges S := hlEq ▸ hlData.2
    obtain ⟨q, hqSpans⟩ :=
      (G.mem_labelledPackingEdges_iff.mp hxyLabelled).2
    rw [G.mem_packingEdgeSpanners_iff] at hqSpans
    have hxyT₂ : ({x, y} : Finset V) ∈ t₂.powersetCard 2 := by
      rw [ht₂Eq]
      exact Finset.mem_powersetCard.mpr ⟨by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        aesop, by simp [hyx.symm]⟩
    have htErase : t ∈ S.erase t₂ :=
      Finset.mem_erase.mpr ⟨htt₂, htS⟩
    exact G.false_of_spanned_edge_and_retained_omitted_vertex (w := u) (p := t)
      hS ht₂S hxyT₂ hqSpans.1 hqSpans.2
      (by rw [ht₂Eq]; simp)
      (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxu.symm, hyu.symm⟩)
      htErase (by rw [htEq]; simp)
  have hlT₂ : l ∈ ({u, x, y} : Finset V).powersetCard 2 := by
    simpa [ht₂Eq] using hlData.1
  have hlEqUy : l = ({u, y} : Finset V) := by
    rcases (mem_powersetCard_two_triple_iff
        hxu.symm hyu.symm hyx.symm).mp hlT₂ with hlEq | hlEq | hlEq
    · exact (hlNeUx hlEq).elim
    · exact hlEq
    · exact (hlNeXy hlEq).elim
  have huyLabelled : ({u, y} : Finset V) ∈
      G.labelledPackingEdges S := hlEqUy ▸ hlData.2
  have ht₂Pretty : t₂ ∈ G.prettyGoodPackingTriangles S := by
    rw [G.mem_prettyGoodPackingTriangles_iff]
    refine ⟨ht₂Good, ?_⟩
    intro hExcellent
    have huxSubR : ({u, x} : Finset V) ⊆ r := by
      rw [hrEq]
      simp
    exact hExcellent.2 huxT₂ huxNotLabelled hrAvoids huxSubR
  exact ⟨huyLabelled, ht₂Pretty⟩

/-- The avoiding triangle is compatible with every packing member left after
removing the two packed triangles that own its two packing edges. -/
theorem card_inter_transfer_witness_le_one_of_two_removed
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    {t t₂ p r : Finset V} (htS : t ∈ S) (ht₂S : t₂ ∈ S)
    (hp : p ∈ (S.erase t).erase t₂)
    {u v w x y : V}
    (huw : u ≠ w) (hxu : x ≠ u) (hxw : x ≠ w)
    (htEq : t = {u, v, w}) (ht₂Eq : t₂ = {u, x, y})
    (hrEq : r = {u, w, x})
    (hwxNot : ({w, x} : Finset V) ∉ triangleFamilyEdges S) :
    (p ∩ r).card ≤ 1 := by
  classical
  by_contra hsmall
  have htwo : 2 ≤ (p ∩ r).card := by omega
  obtain ⟨f, hfSub, hfCard⟩ :=
    Finset.exists_subset_card_eq (s := p ∩ r) (n := 2) htwo
  have hfP : f ∈ p.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_left, hfCard⟩
  have hfR : f ∈ r.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hfSub.trans Finset.inter_subset_right, hfCard⟩
  have hpEraseT : p ∈ S.erase t := Finset.mem_of_mem_erase hp
  have hpS : p ∈ S := Finset.mem_of_mem_erase hpEraseT
  have hfFamily : f ∈ triangleFamilyEdges S := by
    rw [mem_triangleFamilyEdges_iff]
    exact ⟨p, hpS, (Finset.mem_powersetCard.mp hfP).1, hfCard⟩
  have huwT : ({u, w} : Finset V) ∈ t.powersetCard 2 := by
    rw [htEq]
    exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [huw]⟩
  have huxT₂ : ({u, x} : Finset V) ∈ t₂.powersetCard 2 := by
    rw [ht₂Eq]
    exact Finset.mem_powersetCard.mpr ⟨by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop, by simp [hxu.symm]⟩
  rw [hrEq] at hfR
  rcases (mem_powersetCard_two_triple_iff
      huw hxu.symm hxw.symm).mp hfR with hfEq | hfEq | hfEq
  · have hpEq := G.eq_of_mem_powersetCard_of_isTrianglePacking
      hS hpS htS hfP (hfEq ▸ huwT)
    exact (Finset.ne_of_mem_erase hpEraseT) hpEq
  · have hpEq := G.eq_of_mem_powersetCard_of_isTrianglePacking
      hS hpS ht₂S hfP (hfEq ▸ huxT₂)
    exact (Finset.ne_of_mem_erase hp) hpEq
  · exact hwxNot (hfEq ▸ hfFamily)

/-- Spanners of the two labelled edges in the transfer configuration must
coincide; otherwise the two labelled faces and the avoiding triangle give a
three-for-two packing exchange. -/
theorem eq_of_mem_spanners_of_transfer_configuration
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t t₂ r : Finset V} (htS : t ∈ S) (ht₂S : t₂ ∈ S)
    (htt₂ : t ≠ t₂)
    {u v w x y : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w)
    (hyu : y ≠ u) (hyx : y ≠ x)
    (htEq : t = {u, v, w}) (ht₂Eq : t₂ = {u, x, y})
    (hrEq : r = {u, w, x})
    (hrAvoids : G.TriangleAvoidsPackingLabels S r)
    (hwxNot : ({w, x} : Finset V) ∉ triangleFamilyEdges S)
    {q₁ q₂ : V}
    (hq₁ : q₁ ∈ G.packingEdgeSpanners S {u, v})
    (hq₂ : q₂ ∈ G.packingEdgeSpanners S {u, y}) :
    q₁ = q₂ := by
  classical
  rw [G.mem_packingEdgeSpanners_iff] at hq₁ hq₂
  by_contra hqNe
  have hInter : (t ∩ t₂).card ≤ 1 := hS.1.2 htS ht₂S htt₂
  have huT : u ∈ t := by rw [htEq]; simp
  have huT₂ : u ∈ t₂ := by rw [ht₂Eq]; simp
  have hShared : ∀ ⦃z⦄, z ∈ t → z ∈ t₂ → z = u := by
    intro z hzT hzT₂
    by_contra hzu
    have hpairSub : ({u, z} : Finset V) ⊆ t ∩ t₂ := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huT, huT₂⟩
      · exact Finset.mem_inter.mpr ⟨hzT, hzT₂⟩
    have hpairCard : ({u, z} : Finset V).card = 2 := by
      have huz : u ≠ z := fun h ↦ hzu h.symm
      simp [huz]
    have := Finset.card_le_card hpairSub
    omega
  have hyv : y ≠ v := by
    intro hyv
    have hvT : v ∈ t := by rw [htEq]; simp
    have hvT₂ : v ∈ t₂ := by rw [ht₂Eq, hyv]; simp
    exact huv (hShared hvT hvT₂).symm
  have hyw : y ≠ w := by
    intro hyw
    have hwT : w ∈ t := by rw [htEq]; simp
    have hwT₂ : w ∈ t₂ := by rw [ht₂Eq, hyw]; simp
    exact huw (hShared hwT hwT₂).symm
  have hq₁NotT : q₁ ∉ t := by
    intro hqT
    exact hq₁.1 (Finset.mem_biUnion.mpr ⟨t, htS, hqT⟩)
  have hq₁NotT₂ : q₁ ∉ t₂ := by
    intro hqT
    exact hq₁.1 (Finset.mem_biUnion.mpr ⟨t₂, ht₂S, hqT⟩)
  have hq₂NotT : q₂ ∉ t := by
    intro hqT
    exact hq₂.1 (Finset.mem_biUnion.mpr ⟨t, htS, hqT⟩)
  have hq₂NotT₂ : q₂ ∉ t₂ := by
    intro hqT
    exact hq₂.1 (Finset.mem_biUnion.mpr ⟨t₂, ht₂S, hqT⟩)
  have hq₁u : q₁ ≠ u := fun h ↦ hq₁NotT (h ▸ huT)
  have hq₁v : q₁ ≠ v := by
    intro h
    apply hq₁NotT
    rw [htEq, h]
    simp
  have hq₁w : q₁ ≠ w := by
    intro h
    apply hq₁NotT
    rw [htEq, h]
    simp
  have hq₁x : q₁ ≠ x := by
    intro h
    apply hq₁NotT₂
    rw [ht₂Eq, h]
    simp
  have hq₁y : q₁ ≠ y := by
    intro h
    apply hq₁NotT₂
    rw [ht₂Eq, h]
    simp
  have hq₂u : q₂ ≠ u := fun h ↦ hq₂NotT₂ (h ▸ huT₂)
  have hq₂v : q₂ ≠ v := by
    intro h
    apply hq₂NotT
    rw [htEq, h]
    simp
  have hq₂w : q₂ ≠ w := by
    intro h
    apply hq₂NotT
    rw [htEq, h]
    simp
  have hq₂x : q₂ ≠ x := by
    intro h
    apply hq₂NotT₂
    rw [ht₂Eq, h]
    simp
  have hq₂y : q₂ ≠ y := by
    intro h
    apply hq₂NotT₂
    rw [ht₂Eq, h]
    simp
  let a := insert q₁ ({u, v} : Finset V)
  let b := insert q₂ ({u, y} : Finset V)
  have hab : (a ∩ b).card ≤ 1 := by
    simp [a, b, hqNe, hq₁u, hq₁y, hq₂u, hq₂v,
      huv, hyu, hyv]
  have har : (a ∩ r).card ≤ 1 := by
    have hdis : Disjoint ({u, v} : Finset V) {w, x} := by
      rw [Finset.disjoint_left]
      intro z hzLeft hzRight
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft hzRight
      rcases hzLeft with rfl | rfl
      · rcases hzRight with huw' | hux'
        · exact huw huw'
        · exact hxu hux'.symm
      · rcases hzRight with hvw' | hvx'
        · exact hvw hvw'
        · exact hxv hvx'.symm
    have hinterEmpty : ({u, v} : Finset V) ∩ {w, x} = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [hrEq]
    simp [a, hq₁w, hq₁x, hinterEmpty]
  have hbr : (b ∩ r).card ≤ 1 := by
    have hdis : Disjoint ({u, y} : Finset V) {w, x} := by
      rw [Finset.disjoint_left]
      intro z hzLeft hzRight
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft hzRight
      rcases hzLeft with rfl | rfl
      · rcases hzRight with huw' | hux'
        · exact huw huw'
        · exact hxu hux'.symm
      · rcases hzRight with hyw' | hyx'
        · exact hyw hyw'
        · exact hyx hyx'
    have hinterEmpty : ({u, y} : Finset V) ∩ {w, x} = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [hrEq]
    simp [b, hq₂w, hq₂x, hinterEmpty]
  have huvT : ({u, v} : Finset V) ∈ t.powersetCard 2 := by
    rw [htEq]
    exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [huv]⟩
  have huyT₂ : ({u, y} : Finset V) ∈ t₂.powersetCard 2 := by
    rw [ht₂Eq]
    exact Finset.mem_powersetCard.mpr ⟨by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop, by simp [hyu.symm]⟩
  have haR : ∀ ⦃p⦄, p ∈ (S.erase t).erase t₂ →
      (p ∩ a).card ≤ 1 := by
    intro p hp
    have hpEraseT : p ∈ S.erase t := Finset.mem_of_mem_erase hp
    exact G.card_inter_insert_edge_le_one_of_outside hS.1
      (Finset.mem_of_mem_erase hpEraseT) htS
      (Finset.ne_of_mem_erase hpEraseT)
      (Finset.mem_powersetCard.mp huvT).1 hq₁.1
  have hbR : ∀ ⦃p⦄, p ∈ (S.erase t).erase t₂ →
      (p ∩ b).card ≤ 1 := by
    intro p hp
    have hpEraseT : p ∈ S.erase t := Finset.mem_of_mem_erase hp
    exact G.card_inter_insert_edge_le_one_of_outside hS.1
      (Finset.mem_of_mem_erase hpEraseT) ht₂S
      (Finset.ne_of_mem_erase hp)
      (Finset.mem_powersetCard.mp huyT₂).1 hq₂.1
  have hrR : ∀ ⦃p⦄, p ∈ (S.erase t).erase t₂ →
      (p ∩ r).card ≤ 1 := by
    intro p hp
    exact G.card_inter_transfer_witness_le_one_of_two_removed
      hS.1 htS ht₂S hp huw hxu hxw htEq ht₂Eq hrEq hwxNot
  exact G.false_of_three_for_two_exchange hS htS ht₂S htt₂
    hq₁.2 hq₂.2 hrAvoids.1 hab har hbr haR hbR hrR

/-- The two transfer edges have one common spanner, and each of their spanner
sets is exactly that singleton. -/
theorem exists_common_unique_spanner_of_transfer_configuration
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t t₂ r : Finset V} (htS : t ∈ S) (ht₂S : t₂ ∈ S)
    (htt₂ : t ≠ t₂)
    {u v w x y : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w)
    (hyu : y ≠ u) (hyx : y ≠ x)
    (htEq : t = {u, v, w}) (ht₂Eq : t₂ = {u, x, y})
    (hrEq : r = {u, w, x})
    (hrAvoids : G.TriangleAvoidsPackingLabels S r)
    (hwxNot : ({w, x} : Finset V) ∉ triangleFamilyEdges S)
    (huvLabelled : ({u, v} : Finset V) ∈ G.labelledPackingEdges S)
    (huyLabelled : ({u, y} : Finset V) ∈ G.labelledPackingEdges S) :
    ∃ q,
      G.packingEdgeSpanners S {u, v} = {q} ∧
      G.packingEdgeSpanners S {u, y} = {q} := by
  classical
  obtain ⟨q₁, hq₁⟩ :=
    (G.mem_labelledPackingEdges_iff.mp huvLabelled).2
  obtain ⟨q₂, hq₂⟩ :=
    (G.mem_labelledPackingEdges_iff.mp huyLabelled).2
  have hqEq := G.eq_of_mem_spanners_of_transfer_configuration
    hS htS ht₂S htt₂ huv huw hvw hxu hxv hxw hyu hyx
    htEq ht₂Eq hrEq hrAvoids hwxNot hq₁ hq₂
  subst q₂
  refine ⟨q₁, ?_, ?_⟩
  · apply Finset.Subset.antisymm
    · intro z hz
      have hzEq := G.eq_of_mem_spanners_of_transfer_configuration
        hS htS ht₂S htt₂ huv huw hvw hxu hxv hxw hyu hyx
        htEq ht₂Eq hrEq hrAvoids hwxNot hz hq₂
      simp [hzEq]
    · simp [hq₁]
  · apply Finset.Subset.antisymm
    · intro z hz
      have hzEq := G.eq_of_mem_spanners_of_transfer_configuration
        hS htS ht₂S htt₂ huv huw hvw hxu hxv hxw hyu hyx
        htEq ht₂Eq hrEq hrAvoids hwxNot hq₁ hz
      simp [hzEq]
    · simp [hq₂]

/-- Every pretty-good packed triangle determines the adjacent packed triangle
and the avoiding witness used in the component transfer. -/
theorem exists_second_packing_triangle_of_prettyGood
    (G : SimpleGraph V) {S : Finset (Finset V)} {t : Finset V}
    (hS : G.IsSupportMaximalPacking S)
    (htPretty : t ∈ G.prettyGoodPackingTriangles S) :
    ∃ u v w x y : V, ∃ t₂ r : Finset V,
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      x ≠ u ∧ x ≠ v ∧ x ≠ w ∧
      y ≠ u ∧ y ≠ x ∧
      t = {u, v, w} ∧
      ({u, v} : Finset V) ∈ G.labelledPackingEdges S ∧
      r = {u, w, x} ∧ G.TriangleAvoidsPackingLabels S r ∧
      t₂ ∈ S ∧ t ≠ t₂ ∧ t₂ = {u, x, y} ∧
      ({w, x} : Finset V) ∉ triangleFamilyEdges S := by
  classical
  obtain ⟨u, v, w, x, huv, huw, hvw, hxu, hxv, hxw,
      htEq, huvLabelled, r, hrEq, hrAvoids⟩ :=
    G.exists_prettyGood_transfer_configuration hS.1 htPretty
  have htS := (G.mem_goodPackingTriangles_iff.mp
    (G.mem_prettyGoodPackingTriangles_iff.mp htPretty).1).1
  obtain ⟨huxFamily, hwxNot⟩ :=
    G.first_other_edge_mem_and_second_not_mem_of_prettyGood_configuration
      hS htS huv huw hvw hxu hxv hxw htEq huvLabelled hrEq hrAvoids
  obtain ⟨t₂, ht₂S, huxSub, huxCard⟩ :=
    mem_triangleFamilyEdges_iff.mp huxFamily
  have huxT₂ : ({u, x} : Finset V) ∈ t₂.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨huxSub, huxCard⟩
  have hxt : x ∉ t := by
    rw [htEq]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxu, hxv, hxw⟩
  have hxt₂ : x ∈ t₂ := huxSub (by simp)
  have htt₂ : t ≠ t₂ := by
    intro hEq
    exact hxt (hEq ▸ hxt₂)
  have ht₂Card : t₂.card = 3 :=
    G.card_eq_three_of_mem_triangles (hS.1.1 ht₂S)
  obtain ⟨y, hyNotUx, ht₂Insert⟩ :=
    exists_complement_vertex_of_powersetCard_two ht₂Card huxT₂
  have hyu : y ≠ u := fun h ↦ hyNotUx (h ▸ (by simp))
  have hyx : y ≠ x := fun h ↦ hyNotUx (h ▸ (by simp))
  have ht₂Eq : t₂ = {u, x, y} := by
    rw [ht₂Insert]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  exact ⟨u, v, w, x, y, t₂, r,
    huv, huw, hvw, hxu, hxv, hxw, hyu, hyx,
    htEq, huvLabelled, hrEq, hrAvoids, ht₂S, htt₂, ht₂Eq, hwxNot⟩

/-- Every residual pretty-good vertex in an all-good packing component admits
the complete two-edge transfer witness used by the discharge. -/
theorem nonempty_componentTransferWitness
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    (C : (packingIntersectionGraph S).ConnectedComponent)
    (hAllGood : G.IsAllGoodPackingComponent S C)
    {z : V} (hzComponent : z ∈ packingComponentVertexSupport S C)
    (hzResidual : z ∈ G.prettyGoodResidualVertices S) :
    Nonempty (G.ComponentTransferWitness S C z) := by
  classical
  have hzResidualData := G.mem_prettyGoodResidualVertices_iff.mp hzResidual
  obtain ⟨t, htPretty, hzt⟩ :=
    Finset.mem_biUnion.mp hzResidualData.1
  have htGood := (G.mem_prettyGoodPackingTriangles_iff.mp htPretty).1
  have htS := (G.mem_goodPackingTriangles_iff.mp htGood).1
  obtain ⟨s, hsC, hzs⟩ := Finset.mem_biUnion.mp hzComponent
  have htC : t ∈ packingComponentTriangles S C := by
    by_cases hst : s = t
    · simpa [hst] using hsC
    · exact mem_packingComponentTriangles_of_inter_nonempty hsC htS hst
        ⟨z, Finset.mem_inter.mpr ⟨hzs, hzt⟩⟩
  obtain ⟨u, v, w, x, y, t₂, r,
      huv, huw, hvw, hxu, hxv, hxw, hyu, hyx,
      htEq, huvLabelled, hrEq, hrAvoids, ht₂S, htt₂, ht₂Eq, hwxNot⟩ :=
    G.exists_second_packing_triangle_of_prettyGood hS htPretty
  have huLabelledVertex : u ∈ G.labelledPackingVertices S :=
    G.mem_labelledPackingVertices_iff.mpr
      ⟨{u, v}, huvLabelled, by simp⟩
  have hvLabelledVertex : v ∈ G.labelledPackingVertices S :=
    G.mem_labelledPackingVertices_iff.mpr
      ⟨{u, v}, huvLabelled, by simp⟩
  have hzu : z ≠ u := fun h ↦
    hzResidualData.2 (h ▸ huLabelledVertex)
  have hzv : z ≠ v := fun h ↦
    hzResidualData.2 (h ▸ hvLabelledVertex)
  have hzw : z = w := by
    have hzCases : z = u ∨ z = v ∨ z = w := by
      have : z ∈ ({u, v, w} : Finset V) := by simpa [htEq] using hzt
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hzCases with h | h | h
    · exact (hzu h).elim
    · exact (hzv h).elim
    · exact h
  subst z
  have ht₂C : t₂ ∈ packingComponentTriangles S C := by
    apply mem_packingComponentTriangles_of_inter_nonempty htC ht₂S htt₂
    refine ⟨u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [htEq]
      simp
    · rw [ht₂Eq]
      simp
  have ht₂Good : t₂ ∈ G.goodPackingTriangles S := hAllGood ht₂C
  obtain ⟨huyLabelled, ht₂Pretty⟩ :=
    G.second_triangle_labelled_edge_of_prettyGood_configuration
      hS htS ht₂S htt₂ huv huw hvw hxu hxv hxw hyu hyx
      htEq ht₂Eq huvLabelled hrEq hrAvoids ht₂Good
  obtain ⟨q, huvSpanners, huySpanners⟩ :=
    G.exists_common_unique_spanner_of_transfer_configuration
      hS htS ht₂S htt₂ huv huw hvw hxu hxv hxw hyu hyx
      htEq ht₂Eq hrEq hrAvoids hwxNot huvLabelled huyLabelled
  have huvT : ({u, v} : Finset V) ∈ t.powersetCard 2 := by
    rw [htEq]
    exact Finset.mem_powersetCard.mpr ⟨by simp, by simp [huv]⟩
  have huyT₂ : ({u, y} : Finset V) ∈ t₂.powersetCard 2 := by
    rw [ht₂Eq]
    exact Finset.mem_powersetCard.mpr ⟨by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
      aesop, by simp [hyu.symm]⟩
  have hedgesNe : ({u, v} : Finset V) ≠ {u, y} := by
    intro hEdges
    have huvT₂ : ({u, v} : Finset V) ∈ t₂.powersetCard 2 := by
      simpa [hEdges] using huyT₂
    exact htt₂ (G.eq_of_mem_powersetCard_of_isTrianglePacking
      hS.1 htS ht₂S huvT huvT₂)
  exact ⟨{
    firstTriangle := t
    secondTriangle := t₂
    firstEdge := {u, v}
    secondEdge := {u, y}
    spanner := q
    first_mem_component := htC
    second_mem_component := ht₂C
    first_prettyGood := htPretty
    second_prettyGood := ht₂Pretty
    target_mem_first := by rw [htEq]; simp
    first_subset := (Finset.mem_powersetCard.mp huvT).1
    second_subset := (Finset.mem_powersetCard.mp huyT₂).1
    first_labelled := huvLabelled
    second_labelled := huyLabelled
    edges_ne := hedgesNe
    first_spanners := huvSpanners
    second_spanners := huySpanners
  }⟩

end SimpleGraph
