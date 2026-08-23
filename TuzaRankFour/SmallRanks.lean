import Mathlib.Tactic
import TuzaRankFour.Packing

/-!
# Packing numbers at most three

This module specializes Parker's `2`-matching argument to the triangle family
of a finite simple graph. The first lemmas isolate the rank-one intersection
structure used by the later cases.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

omit [Fintype V] in
theorem card_inter_le_one_of_card_eq_two {a b : Finset V}
    (ha : a.card = 2) (hb : b.card = 2) (hne : a ≠ b) :
    (a ∩ b).card ≤ 1 := by
  by_contra h
  have hge : 2 ≤ (a ∩ b).card := by omega
  have hia : a ∩ b = a :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hib : a ∩ b = b :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hne (hia.symm.trans hib)

omit [Fintype V] in
/-- If two three-sets meet in at least two elements but have distinct
two-element traces on a reference set, then their unique elements outside the
reference set agree. -/
theorem sdiff_eq_of_two_le_card_inter_of_distinct_traces
    {a b t : Finset V}
    (ha : (a \ t).card = 1) (hb : (b \ t).card = 1)
    (hat : (a ∩ t).card = 2) (hbt : (b ∩ t).card = 2)
    (hab : 2 ≤ (a ∩ b).card) (htrace : a ∩ t ≠ b ∩ t) :
    a \ t = b \ t := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp ha
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hb
  by_contra hxySet
  have hxy : x ≠ y := by
    intro h
    apply hxySet
    simp [hx, hy, h]
  have hsub : a ∩ b ⊆ (a ∩ t) ∩ (b ∩ t) := by
    intro z hz
    have hzab := Finset.mem_inter.mp hz
    have hzt : z ∈ t := by
      by_contra hznot
      have hzax : z = x := by
        have : z ∈ a \ t := Finset.mem_sdiff.mpr ⟨hzab.1, hznot⟩
        simp [hx] at this
        exact this
      have hzby : z = y := by
        have : z ∈ b \ t := Finset.mem_sdiff.mpr ⟨hzab.2, hznot⟩
        simp [hy] at this
        exact this
      exact hxy (hzax.symm.trans hzby)
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_inter.mpr ⟨hzab.1, hzt⟩,
      Finset.mem_inter.mpr ⟨hzab.2, hzt⟩⟩
  have hsmall := card_inter_le_one_of_card_eq_two hat hbt htrace
  have hmono := Finset.card_le_card hsub
  omega

theorem card_eq_three_of_mem_triangles {t : Finset V} (ht : t ∈ G.triangles) :
    t.card = 3 := by
  have ht' : G.IsNClique 3 t := by simpa [triangles] using ht
  exact ht'.card_eq

/-- Two distinct triangles whose vertex intersection has cardinality at most
one form an edge-disjoint triangle packing. -/
theorem isTrianglePacking_pair {s t : Finset V}
    (hs : s ∈ G.triangles) (ht : t ∈ G.triangles)
    (hst : (s ∩ t).card ≤ 1) :
    G.IsTrianglePacking {s, t} := by
  classical
  constructor
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hs
    · exact ht
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hst
    · simpa [Finset.inter_comm] using hst
    · exact (hab rfl).elim

/-- If `ν(G) ≤ 1`, any two graph triangles share a graph edge. -/
theorem two_le_card_inter_of_packingNumber_le_one
    (hν : G.trianglePackingNumber ≤ 1)
    {s t : Finset V} (hs : s ∈ G.triangles) (ht : t ∈ G.triangles) :
    2 ≤ (s ∩ t).card := by
  classical
  by_contra h
  have hst : (s ∩ t).card ≤ 1 := by omega
  have hpack := G.isTrianglePacking_pair hs ht hst
  have hcard := G.card_le_trianglePackingNumber hpack
  by_cases heq : s = t
  · subst t
    have htri : s.card = 3 := G.card_eq_three_of_mem_triangles hs
    simp [htri] at hst
  · have hpair : ({s, t} : Finset (Finset V)).card = 2 := by simp [heq]
    omega

/-- Distinct triangles in a graph of packing number at most one share exactly
two vertices. -/
theorem card_inter_eq_two_of_packingNumber_le_one
    (hν : G.trianglePackingNumber ≤ 1)
    {s t : Finset V} (hs : s ∈ G.triangles) (ht : t ∈ G.triangles)
    (hne : s ≠ t) :
    (s ∩ t).card = 2 := by
  have hlower := G.two_le_card_inter_of_packingNumber_le_one hν hs ht
  have hsCard := G.card_eq_three_of_mem_triangles hs
  have htCard := G.card_eq_three_of_mem_triangles ht
  have hupper : (s ∩ t).card ≤ 2 := by
    by_contra h
    have hthree : (s ∩ t).card = 3 := by
      have hinter := Finset.card_le_card (Finset.inter_subset_left : s ∩ t ⊆ s)
      omega
    have his : s ∩ t = s :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hit : s ∩ t = t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (his.symm.trans hit)
  omega

/-- A distinct triangle has exactly one vertex outside a fixed triangle when
the packing number is at most one. -/
theorem card_sdiff_eq_one_of_packingNumber_le_one
    (hν : G.trianglePackingNumber ≤ 1)
    {s t : Finset V} (hs : s ∈ G.triangles) (ht : t ∈ G.triangles)
    (hne : s ≠ t) :
    (s \ t).card = 1 := by
  rw [Finset.card_sdiff]
  have hsCard := G.card_eq_three_of_mem_triangles hs
  have hinter := G.card_inter_eq_two_of_packingNumber_le_one hν hs ht hne
  simp [Finset.inter_comm, hsCard, hinter]

/-- The three edges of any fixed triangle cover every triangle when the
packing number is at most one. This is the initial cover before Parker's
rank-one refinement removes one edge. -/
theorem powersetCard_two_isTriangleTransversal
    (hν : G.trianglePackingNumber ≤ 1)
    {t : Finset V} (ht : t ∈ G.triangles) :
    G.IsTriangleTransversal (t.powersetCard 2) := by
  classical
  have ht' : G.IsNClique 3 t := by simpa [triangles] using ht
  constructor
  · intro e he
    rw [edges, mem_cliqueFinset_iff]
    have hep := Finset.mem_powersetCard.mp he
    exact ⟨ht'.isClique.subset (by simpa using hep.1), hep.2⟩
  · intro s hs
    have hinter := G.two_le_card_inter_of_packingNumber_le_one hν hs ht
    obtain ⟨e, hei, hecard⟩ :=
      Finset.exists_subset_card_eq (s := s ∩ t) (n := 2) hinter
    refine ⟨e, Finset.mem_powersetCard.mpr ⟨?_, hecard⟩, ?_⟩
    · exact hei.trans Finset.inter_subset_right
    · exact hei.trans Finset.inter_subset_left

theorem card_powersetCard_two_of_triangle {t : Finset V} (ht : t ∈ G.triangles) :
    (t.powersetCard 2).card = 3 := by
  rw [Finset.card_powersetCard, G.card_eq_three_of_mem_triangles ht]
  decide

/-- A two-set contained in a fixed triangle and in every graph triangle is a
one-edge triangle transversal. -/
theorem singleton_isTriangleTransversal_of_common_pair
    {t e : Finset V} (ht : t ∈ G.triangles)
    (he : e ∈ t.powersetCard 2)
    (hcommon : ∀ ⦃s⦄, s ∈ G.triangles → e ⊆ s) :
    G.IsTriangleTransversal {e} := by
  classical
  have ht' : G.IsNClique 3 t := by simpa [triangles] using ht
  have hep := Finset.mem_powersetCard.mp he
  constructor
  · intro f hf
    simp only [Finset.mem_singleton] at hf
    subst f
    rw [edges, mem_cliqueFinset_iff]
    exact ⟨ht'.isClique.subset (by simpa using hep.1), hep.2⟩
  · intro s hs
    exact ⟨e, Finset.mem_singleton_self e, hcommon hs⟩

/-- A two-subset of a graph triangle is a graph edge. -/
theorem mem_edges_of_subset_triangle {e t : Finset V}
    (ht : t ∈ G.triangles) (het : e ⊆ t) (hecard : e.card = 2) :
    e ∈ G.edges := by
  classical
  have ht' : G.IsNClique 3 t := by simpa [triangles] using ht
  rw [edges, mem_cliqueFinset_iff]
  exact ⟨ht'.isClique.subset (by simpa using het), hecard⟩

omit [Fintype V] in
/-- If `r` is a two-subset of a three-set `t`, then every set meeting `t` in
at least two points either contains `r` or contains the unique point of
`t \ r`. -/
theorem subset_or_mem_of_large_trace {r t s : Finset V} {a : V}
    (hrcard : r.card = 2) (htr : t \ r = {a})
    (htrace : 2 ≤ (s ∩ t).card) :
    r ⊆ s ∨ a ∈ s := by
  classical
  by_cases ha : a ∈ s
  · exact Or.inr ha
  · left
    have hsub : s ∩ t ⊆ r := by
      intro z hz
      by_contra hzr
      have hzdiff : z ∈ t \ r :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz).2, hzr⟩
      have hza : z = a := by simpa [htr] using hzdiff
      exact ha (hza ▸ (Finset.mem_inter.mp hz).1)
    have heq : s ∩ t = r :=
      Finset.eq_of_subset_of_card_le hsub (by
        have hle := Finset.card_le_card hsub
        omega)
    rw [← heq]
    exact Finset.inter_subset_left

/-- Parker's rank-one dichotomy, specialized to graph triangles. Either a
pair of vertices of `t` belongs to every triangle, or all other triangles
have the same unique vertex outside `t`. -/
theorem common_pair_or_common_outside_vertex
    (hν : G.trianglePackingNumber ≤ 1)
    {t : Finset V} (ht : t ∈ G.triangles) :
    (∃ e ∈ t.powersetCard 2,
        ∀ ⦃s⦄, s ∈ G.triangles → e ⊆ s) ∨
      ∃ v ∉ t,
        (∀ e ∈ t.powersetCard 2,
          ∃ s ∈ G.triangles, ¬ e ⊆ s) ∧
        ∀ ⦃s⦄, s ∈ G.triangles → s ≠ t → s \ t = {v} := by
  classical
  by_cases hcommon :
      ∃ e ∈ t.powersetCard 2,
        ∀ ⦃s⦄, s ∈ G.triangles → e ⊆ s
  · exact Or.inl hcommon
  · right
    have hmiss (e : Finset V) (he : e ∈ t.powersetCard 2) :
        ∃ s ∈ G.triangles, ¬ e ⊆ s := by
      by_contra h
      apply hcommon
      refine ⟨e, he, ?_⟩
      intro s hs
      by_contra hes
      exact h ⟨s, hs, hes⟩
    have hpowCard : (t.powersetCard 2).card = 3 :=
      G.card_powersetCard_two_of_triangle ht
    obtain ⟨e, he⟩ : (t.powersetCard 2).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      simp [hempty] at hpowCard
    obtain ⟨f, hf, hef⟩ := hmiss e he
    have hft : f ≠ t := by
      intro hft
      subst f
      exact hef (Finset.mem_powersetCard.mp he).1
    have hfoutCard :=
      G.card_sdiff_eq_one_of_packingNumber_le_one hν hf ht hft
    obtain ⟨v, hfv⟩ := Finset.card_eq_one.mp hfoutCard
    have hvout : v ∈ f \ t := by simp [hfv]
    refine ⟨v, (Finset.mem_sdiff.mp hvout).2, hmiss, ?_⟩
    intro s hs hst
    have hsoutCard :=
      G.card_sdiff_eq_one_of_packingNumber_le_one hν hs ht hst
    have hftraceCard :=
      G.card_inter_eq_two_of_packingNumber_le_one hν hf ht hft
    have hstraceCard :=
      G.card_inter_eq_two_of_packingNumber_le_one hν hs ht hst
    have hfs := G.two_le_card_inter_of_packingNumber_le_one hν hf hs
    have houtside : f \ t = s \ t := by
      by_cases htrace : f ∩ t = s ∩ t
      · obtain ⟨u, hu, hfu⟩ := hmiss (f ∩ t) (by
          exact Finset.mem_powersetCard.mpr
            ⟨Finset.inter_subset_right, hftraceCard⟩)
        have hut : u ≠ t := by
          intro hut
          subst u
          exact hfu Finset.inter_subset_right
        have hutraceCard :=
          G.card_inter_eq_two_of_packingNumber_le_one hν hu ht hut
        have hfuTrace : f ∩ t ≠ u ∩ t := by
          intro heq
          apply hfu
          rw [heq]
          exact Finset.inter_subset_left
        have hsuTrace : s ∩ t ≠ u ∩ t := by
          intro heq
          exact hfuTrace (htrace.trans heq)
        have hfuInter := G.two_le_card_inter_of_packingNumber_le_one hν hf hu
        have hsuInter := G.two_le_card_inter_of_packingNumber_le_one hν hs hu
        have hfuOutside :=
          sdiff_eq_of_two_le_card_inter_of_distinct_traces
            hfoutCard
            (G.card_sdiff_eq_one_of_packingNumber_le_one hν hu ht hut)
            hftraceCard hutraceCard hfuInter hfuTrace
        have hsuOutside :=
          sdiff_eq_of_two_le_card_inter_of_distinct_traces
            hsoutCard
            (G.card_sdiff_eq_one_of_packingNumber_le_one hν hu ht hut)
            hstraceCard hutraceCard hsuInter hsuTrace
        exact hfuOutside.trans hsuOutside.symm
      · exact sdiff_eq_of_two_le_card_inter_of_distinct_traces
          hfoutCard hsoutCard hftraceCard hstraceCard hfs htrace
    exact houtside.symm.trans hfv

/-- The common-outside-vertex branch of the rank-one dichotomy has a
two-edge triangle transversal. -/
theorem two_edge_transversal_of_common_outside_vertex
    (hν : G.trianglePackingNumber ≤ 1)
    {t : Finset V} (ht : t ∈ G.triangles)
    {v : V} (hv : v ∉ t)
    (hmiss : ∀ e ∈ t.powersetCard 2,
      ∃ s ∈ G.triangles, ¬ e ⊆ s)
    (htip : ∀ ⦃s⦄, s ∈ G.triangles → s ≠ t → s \ t = {v}) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 2 := by
  classical
  have hpowCard : (t.powersetCard 2).card = 3 :=
    G.card_powersetCard_two_of_triangle ht
  obtain ⟨r, hr⟩ : (t.powersetCard 2).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    simp [hempty] at hpowCard
  have hrdata := Finset.mem_powersetCard.mp hr
  have htdiffCard : (t \ r).card = 1 := by
    rw [Finset.card_sdiff]
    have hinter : r ∩ t = r := Finset.inter_eq_left.mpr hrdata.1
    rw [hinter, G.card_eq_three_of_mem_triangles ht, hrdata.2]
  obtain ⟨a, hta⟩ := Finset.card_eq_one.mp htdiffCard
  have hat : a ∈ t := by
    have : a ∈ t \ r := by simp [hta]
    exact (Finset.mem_sdiff.mp this).1
  obtain ⟨s, hs, hrs⟩ := hmiss r hr
  have hst : s ≠ t := by
    intro hst
    subst s
    exact hrs hrdata.1
  have hsTrace := G.two_le_card_inter_of_packingNumber_le_one hν hs ht
  have has : a ∈ s := by
    rcases subset_or_mem_of_large_trace hrdata.2 hta hsTrace with hrs' | has
    · exact (hrs hrs').elim
    · exact has
  have hvdiff : v ∈ s \ t := by
    rw [htip hs hst]
    simp
  have havSubset : {a, v} ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact has
    · exact (Finset.mem_sdiff.mp hvdiff).1
  have hav : a ≠ v := by
    intro hav
    exact hv (hav ▸ hat)
  have havCard : ({a, v} : Finset V).card = 2 := by simp [hav]
  let C : Finset (Finset V) := {r, {a, v}}
  refine ⟨C, ?_, ?_⟩
  · constructor
    · intro e he
      simp only [C, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact G.mem_edges_of_subset_triangle ht hrdata.1 hrdata.2
      · exact G.mem_edges_of_subset_triangle hs havSubset havCard
    · intro q hq
      by_cases hqt : q = t
      · subst q
        exact ⟨r, by simp [C], hrdata.1⟩
      · have hqTrace := G.two_le_card_inter_of_packingNumber_le_one hν hq ht
        rcases subset_or_mem_of_large_trace hrdata.2 hta hqTrace with
          hrq | haq
        · exact ⟨r, by simp [C], hrq⟩
        · have hvq : v ∈ q := by
            have : v ∈ q \ t := by
              rw [htip hq hqt]
              simp
            exact (Finset.mem_sdiff.mp this).1
          refine ⟨{a, v}, by simp [C], ?_⟩
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          exact hz.elim (fun h ↦ h ▸ haq) (fun h ↦ h ▸ hvq)
  · change ({r, {a, v}} : Finset (Finset V)).card ≤ 2
    exact Finset.card_le_two

/-- Tuza's inequality for graphs with triangle-packing number at most one. -/
theorem tuza_of_trianglePackingNumber_le_one
    (hν : G.trianglePackingNumber ≤ 1) :
    G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber := by
  classical
  by_cases hzero : G.trianglePackingNumber = 0
  · obtain ⟨C, hC, hcard⟩ :=
      G.exists_triangleTransversal_of_packingNumber_eq_zero hzero
    exact (G.triangleTransversalNumber_le_card hC).trans hcard
  · have hνeq : G.trianglePackingNumber = 1 := by omega
    have htri : G.triangles.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      exact hzero (G.trianglePackingNumber_eq_zero_iff.mpr hempty)
    obtain ⟨t, ht⟩ := htri
    rcases G.common_pair_or_common_outside_vertex hν ht with
      ⟨e, he, hcommon⟩ | ⟨v, hv, hmiss, htip⟩
    · have hC := G.singleton_isTriangleTransversal_of_common_pair ht he hcommon
      have hτ := G.triangleTransversalNumber_le_card hC
      exact hτ.trans (by simp [hνeq])
    · obtain ⟨C, hC, hcard⟩ :=
        G.two_edge_transversal_of_common_outside_vertex hν ht hv hmiss htip
      have hτ := (G.triangleTransversalNumber_le_card hC).trans hcard
      simpa [hνeq] using hτ

end SimpleGraph
