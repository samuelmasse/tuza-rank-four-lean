import TuzaRankFour.SmallRanks

/-!
# Parker's bounded two-matching theorem

This module formalizes the three-uniform part of Parker's argument.  A
triangle subfamily is covered by two-element subsets of its members; because
the members are graph triangles, every such subset is automatically a graph
edge.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- `C` covers the triangle subfamily `F` by graph edges. -/
def IsTriangleFamilyTransversal
    (F C : Finset (Finset V)) : Prop :=
  C ⊆ G.edges ∧ ∀ ⦃t⦄, t ∈ F → ∃ e ∈ C, e ⊆ t

omit [Fintype V] in
/-- Two distinct three-sets that meet in at least two points meet in exactly
two points. -/
theorem card_inter_eq_two_of_card_eq_three
    {s t : Finset V} (hsCard : s.card = 3) (htCard : t.card = 3)
    (hne : s ≠ t) (hlower : 2 ≤ (s ∩ t).card) :
    (s ∩ t).card = 2 := by
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

omit [Fintype V] in
/-- A distinct three-set has one point outside another three-set when their
intersection has cardinality at least two. -/
theorem card_sdiff_eq_one_of_card_eq_three
    {s t : Finset V} (hsCard : s.card = 3) (htCard : t.card = 3)
    (hne : s ≠ t) (hlower : 2 ≤ (s ∩ t).card) :
    (s \ t).card = 1 := by
  rw [Finset.card_sdiff]
  have hinter := card_inter_eq_two_of_card_eq_three hsCard htCard hne hlower
  simp [Finset.inter_comm, hsCard, hinter]

/-- Rank-one structure for an arbitrary pairwise two-intersecting family of
graph triangles, with a designated member `t`. -/
theorem family_common_pair_or_common_outside_vertex
    {F : Finset (Finset V)} (hF : F ⊆ G.triangles)
    (hpair : ∀ ⦃s⦄, s ∈ F → ∀ ⦃u⦄, u ∈ F → 2 ≤ (s ∩ u).card)
    {t : Finset V} (htF : t ∈ F) :
    (∃ e ∈ t.powersetCard 2, ∀ ⦃s⦄, s ∈ F → e ⊆ s) ∨
      ∃ v ∉ t, ∀ ⦃s⦄, s ∈ F → s ≠ t → s \ t = {v} := by
  classical
  have ht := hF htF
  have htCard := G.card_eq_three_of_mem_triangles ht
  by_cases hcommon :
      ∃ e ∈ t.powersetCard 2, ∀ ⦃s⦄, s ∈ F → e ⊆ s
  · exact Or.inl hcommon
  · right
    have hmiss (e : Finset V) (he : e ∈ t.powersetCard 2) :
        ∃ s ∈ F, ¬ e ⊆ s := by
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
    obtain ⟨f, hfF, hef⟩ := hmiss e he
    have hf := hF hfF
    have hfCard := G.card_eq_three_of_mem_triangles hf
    have hft : f ≠ t := by
      intro hft
      subst f
      exact hef (Finset.mem_powersetCard.mp he).1
    have hftLower := hpair hfF htF
    have hftraceCard :=
      card_inter_eq_two_of_card_eq_three hfCard htCard hft hftLower
    have hfoutCard :=
      card_sdiff_eq_one_of_card_eq_three hfCard htCard hft hftLower
    obtain ⟨v, hfv⟩ := Finset.card_eq_one.mp hfoutCard
    have hvout : v ∈ f \ t := by simp [hfv]
    refine ⟨v, (Finset.mem_sdiff.mp hvout).2, ?_⟩
    intro s hsF hst
    have hs := hF hsF
    have hsCard := G.card_eq_three_of_mem_triangles hs
    have hstLower := hpair hsF htF
    have hsoutCard :=
      card_sdiff_eq_one_of_card_eq_three hsCard htCard hst hstLower
    have hstraceCard :=
      card_inter_eq_two_of_card_eq_three hsCard htCard hst hstLower
    have hfs := hpair hfF hsF
    have houtside : f \ t = s \ t := by
      by_cases htrace : f ∩ t = s ∩ t
      · obtain ⟨u, huF, hfu⟩ := hmiss (f ∩ t) (by
          exact Finset.mem_powersetCard.mpr
            ⟨Finset.inter_subset_right, hftraceCard⟩)
        have hu := hF huF
        have huCard := G.card_eq_three_of_mem_triangles hu
        have hut : u ≠ t := by
          intro hut
          subst u
          exact hfu Finset.inter_subset_right
        have hutLower := hpair huF htF
        have hutraceCard :=
          card_inter_eq_two_of_card_eq_three huCard htCard hut hutLower
        have huoutCard :=
          card_sdiff_eq_one_of_card_eq_three huCard htCard hut hutLower
        have hfuTrace : f ∩ t ≠ u ∩ t := by
          intro heq
          apply hfu
          rw [heq]
          exact Finset.inter_subset_left
        have hsuTrace : s ∩ t ≠ u ∩ t := by
          intro heq
          exact hfuTrace (htrace.trans heq)
        have hfuOutside :=
          sdiff_eq_of_two_le_card_inter_of_distinct_traces
            hfoutCard huoutCard hftraceCard hutraceCard
            (hpair hfF huF) hfuTrace
        have hsuOutside :=
          sdiff_eq_of_two_le_card_inter_of_distinct_traces
            hsoutCard huoutCard hstraceCard hutraceCard
            (hpair hsF huF) hsuTrace
        exact hfuOutside.trans hsuOutside.symm
      · exact sdiff_eq_of_two_le_card_inter_of_distinct_traces
          hfoutCard hsoutCard hftraceCard hstraceCard hfs htrace
    exact houtside.symm.trans hfv

/-- Every nonempty pairwise two-intersecting family of graph triangles has a
two-edge transversal.  This is the `k = 3` content of Parker's rank-one
lemma, stated for a subfamily so it can be reused in the rank-two and
rank-three decompositions. -/
theorem exists_two_family_transversal_of_pairwise_two_intersecting
    {F : Finset (Finset V)} (hF : F ⊆ G.triangles) (hFne : F.Nonempty)
    (hpair : ∀ ⦃s⦄, s ∈ F → ∀ ⦃t⦄, t ∈ F → 2 ≤ (s ∩ t).card) :
    ∃ C : Finset (Finset V),
      G.IsTriangleFamilyTransversal F C ∧ C.card ≤ 2 := by
  classical
  obtain ⟨t, htF⟩ := hFne
  have ht := hF htF
  have htCard := G.card_eq_three_of_mem_triangles ht
  by_cases hcommon :
      ∃ e ∈ t.powersetCard 2, ∀ ⦃s⦄, s ∈ F → e ⊆ s
  · obtain ⟨e, he, hecommon⟩ := hcommon
    refine ⟨{e}, ?_, by simp⟩
    constructor
    · intro f hf
      simp only [Finset.mem_singleton] at hf
      subst f
      have hedata := Finset.mem_powersetCard.mp he
      exact G.mem_edges_of_subset_triangle ht hedata.1 hedata.2
    · intro s hs
      exact ⟨e, Finset.mem_singleton_self e, hecommon hs⟩
  · have hmiss (e : Finset V) (he : e ∈ t.powersetCard 2) :
        ∃ s ∈ F, ¬ e ⊆ s := by
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
    obtain ⟨f, hfF, hef⟩ := hmiss e he
    have hf := hF hfF
    have hfCard := G.card_eq_three_of_mem_triangles hf
    have hft : f ≠ t := by
      intro hft
      subst f
      exact hef (Finset.mem_powersetCard.mp he).1
    have hftLower := hpair hfF htF
    have hftraceCard :=
      card_inter_eq_two_of_card_eq_three hfCard htCard hft hftLower
    have hfoutCard :=
      card_sdiff_eq_one_of_card_eq_three hfCard htCard hft hftLower
    obtain ⟨v, hfv⟩ := Finset.card_eq_one.mp hfoutCard
    have hvout : v ∈ f \ t := by simp [hfv]
    have hv : v ∉ t := (Finset.mem_sdiff.mp hvout).2
    have htip : ∀ ⦃s⦄, s ∈ F → s ≠ t → s \ t = {v} := by
      intro s hsF hst
      have hs := hF hsF
      have hsCard := G.card_eq_three_of_mem_triangles hs
      have hstLower := hpair hsF htF
      have hsoutCard :=
        card_sdiff_eq_one_of_card_eq_three hsCard htCard hst hstLower
      have hstraceCard :=
        card_inter_eq_two_of_card_eq_three hsCard htCard hst hstLower
      have hfs := hpair hfF hsF
      have houtside : f \ t = s \ t := by
        by_cases htrace : f ∩ t = s ∩ t
        · obtain ⟨u, huF, hfu⟩ := hmiss (f ∩ t) (by
            exact Finset.mem_powersetCard.mpr
              ⟨Finset.inter_subset_right, hftraceCard⟩)
          have hu := hF huF
          have huCard := G.card_eq_three_of_mem_triangles hu
          have hut : u ≠ t := by
            intro hut
            subst u
            exact hfu Finset.inter_subset_right
          have hutLower := hpair huF htF
          have hutraceCard :=
            card_inter_eq_two_of_card_eq_three huCard htCard hut hutLower
          have huoutCard :=
            card_sdiff_eq_one_of_card_eq_three huCard htCard hut hutLower
          have hfuTrace : f ∩ t ≠ u ∩ t := by
            intro heq
            apply hfu
            rw [heq]
            exact Finset.inter_subset_left
          have hsuTrace : s ∩ t ≠ u ∩ t := by
            intro heq
            exact hfuTrace (htrace.trans heq)
          have hfuOutside :=
            sdiff_eq_of_two_le_card_inter_of_distinct_traces
              hfoutCard huoutCard hftraceCard hutraceCard
              (hpair hfF huF) hfuTrace
          have hsuOutside :=
            sdiff_eq_of_two_le_card_inter_of_distinct_traces
              hsoutCard huoutCard hstraceCard hutraceCard
              (hpair hsF huF) hsuTrace
          exact hfuOutside.trans hsuOutside.symm
        · exact sdiff_eq_of_two_le_card_inter_of_distinct_traces
            hfoutCard hsoutCard hftraceCard hstraceCard hfs htrace
      exact houtside.symm.trans hfv
    have htdiffCard : (t \ (f ∩ t)).card = 1 := by
      rw [Finset.card_sdiff]
      have hinter : (f ∩ t) ∩ t = f ∩ t :=
        Finset.inter_eq_left.mpr Finset.inter_subset_right
      rw [hinter, htCard, hftraceCard]
    obtain ⟨a, hta⟩ := Finset.card_eq_one.mp htdiffCard
    have hat : a ∈ t := by
      have : a ∈ t \ (f ∩ t) := by simp [hta]
      exact (Finset.mem_sdiff.mp this).1
    obtain ⟨s, hsF, hfsMiss⟩ := hmiss (f ∩ t) (by
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.inter_subset_right, hftraceCard⟩)
    have hs := hF hsF
    have hst : s ≠ t := by
      intro hst
      subst s
      exact hfsMiss Finset.inter_subset_right
    have hsTrace := hpair hsF htF
    have has : a ∈ s := by
      rcases subset_or_mem_of_large_trace hftraceCard hta hsTrace with
        hfsSubset | has
      · exact (hfsMiss hfsSubset).elim
      · exact has
    have hvdiff : v ∈ s \ t := by
      rw [htip hsF hst]
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
    let C : Finset (Finset V) := {f ∩ t, {a, v}}
    refine ⟨C, ?_, ?_⟩
    · constructor
      · intro d hd
        simp only [C, Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact G.mem_edges_of_subset_triangle ht
            Finset.inter_subset_right hftraceCard
        · exact G.mem_edges_of_subset_triangle hs havSubset havCard
      · intro q hqF
        by_cases hqt : q = t
        · subst q
          exact ⟨f ∩ t, by simp [C], Finset.inter_subset_right⟩
        · have hqTrace := hpair hqF htF
          rcases subset_or_mem_of_large_trace hftraceCard hta hqTrace with
            hfq | haq
          · exact ⟨f ∩ t, by simp [C], hfq⟩
          · have hvq : v ∈ q := by
              have : v ∈ q \ t := by
                rw [htip hqF hqt]
                simp
              exact (Finset.mem_sdiff.mp this).1
            refine ⟨{a, v}, by simp [C], ?_⟩
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            exact hz.elim (fun h ↦ h ▸ haq) (fun h ↦ h ▸ hvq)
    · change ({f ∩ t, {a, v}} : Finset (Finset V)).card ≤ 2
      exact Finset.card_le_two

/-- The two-subsets of `t` containing `x`. -/
def pairsThrough (t : Finset V) (x : V) : Finset (Finset V) :=
  (t.powersetCard 2).filter fun p ↦ x ∈ p

omit [Fintype V] in
theorem card_pairsThrough_le_two {t : Finset V} {x : V}
    (htCard : t.card = 3) (hx : x ∈ t) :
    (pairsThrough t x).card ≤ 2 := by
  classical
  have heraseCard : (t.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx, htCard]
  have herasePow : t.erase x ∈ t.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨Finset.erase_subset x t, heraseCard⟩
  have heraseNot : t.erase x ∉ pairsThrough t x := by
    simp [pairsThrough]
  have hsub : pairsThrough t x ⊆ t.powersetCard 2 := by
    exact Finset.filter_subset _ _
  have hpCard : (t.powersetCard 2).card = 3 := by
    rw [Finset.card_powersetCard, htCard]
    decide
  by_contra h
  have hle := Finset.card_le_card hsub
  have heqCard : (pairsThrough t x).card = 3 := by omega
  have heq : pairsThrough t x = t.powersetCard 2 :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact heraseNot (heq ▸ herasePow)

/-- Pairs of `t` through `x` cover every family member that contains `x`
and meets `t` in at least two vertices. -/
theorem pairsThrough_is_family_transversal
    {F : Finset (Finset V)} {t : Finset V} {x : V}
    (ht : t ∈ G.triangles) (hx : x ∈ t)
    (hnear : ∀ ⦃q⦄, q ∈ F → 2 ≤ (q ∩ t).card)
    (hxall : ∀ ⦃q⦄, q ∈ F → x ∈ q) :
    G.IsTriangleFamilyTransversal F (pairsThrough t x) := by
  classical
  constructor
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpdata := Finset.mem_powersetCard.mp hp'.1
    exact G.mem_edges_of_subset_triangle ht hpdata.1 hpdata.2
  · intro q hq
    have hxqt : x ∈ q ∩ t := Finset.mem_inter.mpr ⟨hxall hq, hx⟩
    have herasePos : 0 < ((q ∩ t).erase x).card := by
      rw [Finset.card_erase_of_mem hxqt]
      have := hnear hq
      omega
    obtain ⟨y, hy⟩ : ((q ∩ t).erase x).Nonempty :=
      Finset.card_pos.mp herasePos
    have hyqt : y ∈ q ∩ t := (Finset.mem_erase.mp hy).2
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    let p : Finset V := {x, y}
    have hpCard : p.card = 2 := by simp [p, hyx.symm]
    have hpt : p ⊆ t := by
      intro z hz
      simp only [p, Finset.mem_insert, Finset.mem_singleton] at hz
      exact hz.elim (fun h ↦ h ▸ hx)
        (fun h ↦ h ▸ (Finset.mem_inter.mp hyqt).2)
    have hpq : p ⊆ q := by
      intro z hz
      simp only [p, Finset.mem_insert, Finset.mem_singleton] at hz
      exact hz.elim (fun h ↦ h ▸ hxall hq)
        (fun h ↦ h ▸ (Finset.mem_inter.mp hyqt).1)
    refine ⟨p, ?_, hpq⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hpt, hpCard⟩, by simp [p]⟩

/-- The three pairs of `t` cover every family member meeting `t` in at
least two vertices. -/
theorem powersetCard_two_is_family_transversal
    {F : Finset (Finset V)} {t : Finset V}
    (ht : t ∈ G.triangles)
    (hnear : ∀ ⦃q⦄, q ∈ F → 2 ≤ (q ∩ t).card) :
    G.IsTriangleFamilyTransversal F (t.powersetCard 2) := by
  classical
  constructor
  · intro p hp
    have hpdata := Finset.mem_powersetCard.mp hp
    exact G.mem_edges_of_subset_triangle ht hpdata.1 hpdata.2
  · intro q hq
    obtain ⟨p, hp, hpCard⟩ :=
      Finset.exists_subset_card_eq (s := q ∩ t) (n := 2) (hnear hq)
    exact ⟨p, Finset.mem_powersetCard.mpr
      ⟨hp.trans Finset.inter_subset_right, hpCard⟩,
      hp.trans Finset.inter_subset_left⟩

omit [Fintype V] in
/-- If two three-sets meet exactly in `x`, any three-set meeting each in at
least two points contains `x`. -/
theorem mem_common_of_two_large_intersections
    {e f q : Finset V} {x : V}
    (heCard : e.card = 3) (hfCard : f.card = 3) (hqCard : q.card = 3)
    (hef : e ∩ f = {x})
    (hqe : 2 ≤ (q ∩ e).card) (hqf : 2 ≤ (q ∩ f).card) :
    x ∈ q := by
  classical
  by_contra hxq
  have hxe : x ∈ e := by
    have : x ∈ e ∩ f := by simp [hef]
    exact (Finset.mem_inter.mp this).1
  have hxf : x ∈ f := by
    have : x ∈ e ∩ f := by simp [hef]
    exact (Finset.mem_inter.mp this).2
  have heEraseCard : (e.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxe, heCard]
  have hfEraseCard : (f.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxf, hfCard]
  have hqeSub : q ∩ e ⊆ e.erase x := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨by
      intro hzx
      exact hxq (hzx ▸ (Finset.mem_inter.mp hz).1),
      (Finset.mem_inter.mp hz).2⟩
  have hqfSub : q ∩ f ⊆ f.erase x := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨by
      intro hzx
      exact hxq (hzx ▸ (Finset.mem_inter.mp hz).1),
      (Finset.mem_inter.mp hz).2⟩
  have hqeEq : q ∩ e = e.erase x :=
    Finset.eq_of_subset_of_card_le hqeSub (by omega)
  have hqfEq : q ∩ f = f.erase x :=
    Finset.eq_of_subset_of_card_le hqfSub (by omega)
  have hdisj : Disjoint (e.erase x) (f.erase x) := by
    rw [Finset.disjoint_left]
    intro z hze hzf
    have hzef : z ∈ e ∩ f := Finset.mem_inter.mpr
      ⟨(Finset.mem_erase.mp hze).2, (Finset.mem_erase.mp hzf).2⟩
    have hzx : z = x := by simpa [hef] using hzef
    exact (Finset.mem_erase.mp hze).1 hzx
  have hsub : (e.erase x) ∪ (f.erase x) ⊆ q := by
    rw [← hqeEq, ← hqfEq]
    exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, heEraseCard, hfEraseCard, hqCard] at hcard
  omega

omit [Fintype V] in
/-- A three-set that meets one of two disjoint sets in at least two points
meets the other in at most one point. -/
theorem card_inter_le_one_of_disjoint_of_large_inter
    {q e f : Finset V} (hqCard : q.card = 3)
    (hef : Disjoint e f) (hqe : 2 ≤ (q ∩ e).card) :
    (q ∩ f).card ≤ 1 := by
  have hdisj : Disjoint (q ∩ e) (q ∩ f) := by
    rw [Finset.disjoint_left]
    intro x hxe hxf
    exact (Finset.disjoint_left.mp hef)
      (Finset.mem_inter.mp hxe).2 (Finset.mem_inter.mp hxf).2
  have hsub : (q ∩ e) ∪ (q ∩ f) ⊆ q := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).1
    · exact (Finset.mem_inter.mp hx).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hqCard] at hcard
  omega

/-- Three graph triangles with pairwise intersections of cardinality at most
one form a triangle packing. -/
theorem isTrianglePacking_triple {r s t : Finset V}
    (hr : r ∈ G.triangles) (hs : s ∈ G.triangles)
    (ht : t ∈ G.triangles)
    (hrs : (r ∩ s).card ≤ 1) (hrt : (r ∩ t).card ≤ 1)
    (hst : (s ∩ t).card ≤ 1) :
    G.IsTrianglePacking {r, s, t} := by
  classical
  constructor
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hr
    · exact hs
    · exact ht
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact hrs
    · exact hrt
    · simpa [Finset.inter_comm] using hrs
    · exact (hab rfl).elim
    · exact hst
    · simpa [Finset.inter_comm] using hrt
    · simpa [Finset.inter_comm] using hst
    · exact (hab rfl).elim

/-- Triangles sharing a graph edge with `t`. -/
noncomputable def nearTriangles (t : Finset V) : Finset (Finset V) := by
  classical
  exact G.triangles.filter fun q ↦ 2 ≤ (q ∩ t).card

/-- Triangles sharing a graph edge with `e` but no graph edge with `f`. -/
noncomputable def privateTriangles
    (e f : Finset V) : Finset (Finset V) := by
  classical
  exact G.triangles.filter fun q ↦
    2 ≤ (q ∩ e).card ∧ (q ∩ f).card ≤ 1

/-- Maximality of a two-packing: every triangle shares an edge with one of
its two members. -/
theorem near_one_of_packing_pair
    (hν : G.trianglePackingNumber ≤ 2)
    {e f q : Finset V} (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hq : q ∈ G.triangles) (hef : (e ∩ f).card ≤ 1) :
    2 ≤ (q ∩ e).card ∨ 2 ≤ (q ∩ f).card := by
  classical
  by_contra h
  push Not at h
  have hqe : (q ∩ e).card ≤ 1 := by omega
  have hqf : (q ∩ f).card ≤ 1 := by omega
  have hpack := G.isTrianglePacking_triple he hf hq hef
    (by simpa [Finset.inter_comm] using hqe)
    (by simpa [Finset.inter_comm] using hqf)
  have hpackCard := G.card_le_trianglePackingNumber hpack
  have hefNe : e ≠ f := by
    intro h
    subst f
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at hef
  have heqNe : e ≠ q := by
    intro h
    subst q
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at hqe
  have hfqNe : f ≠ q := by
    intro h
    subst q
    have hfCard := G.card_eq_three_of_mem_triangles hf
    simp [hfCard] at hqf
  have hcard : ({e, f, q} : Finset (Finset V)).card = 3 := by
    simp [hefNe, heqNe, hfqNe]
  omega

/-- The private family of one member of a maximum two-packing is pairwise
two-intersecting. -/
theorem privateTriangles_pairwise_two_intersecting
    (hν : G.trianglePackingNumber ≤ 2)
    {e f : Finset V} (hf : f ∈ G.triangles) :
    ∀ ⦃q⦄, q ∈ G.privateTriangles e f →
      ∀ ⦃r⦄, r ∈ G.privateTriangles e f → 2 ≤ (q ∩ r).card := by
  classical
  intro q hqP r hrP
  have hqData := Finset.mem_filter.mp hqP
  have hrData := Finset.mem_filter.mp hrP
  by_contra hqr
  have hqr' : (q ∩ r).card ≤ 1 := by omega
  have hpack := G.isTrianglePacking_triple hqData.1 hrData.1 hf hqr'
    hqData.2.2 hrData.2.2
  have hpackCard := G.card_le_trianglePackingNumber hpack
  have hqfNe : q ≠ f := by
    intro h
    subst q
    have hfCard := G.card_eq_three_of_mem_triangles hf
    simp [hfCard] at hqData
  have hrfNe : r ≠ f := by
    intro h
    subst r
    have hfCard := G.card_eq_three_of_mem_triangles hf
    simp [hfCard] at hrData
  have hqrNe : q ≠ r := by
    intro h
    subst r
    have hqCard := G.card_eq_three_of_mem_triangles hqData.1
    simp [hqCard] at hqr'
  have hcard : ({q, r, f} : Finset (Finset V)).card = 3 := by
    simp [hqfNe, hrfNe, hqrNe]
  omega

/-- Parker's disconnected-packing case for a two-matching of graph
triangles. -/
theorem exists_four_transversal_of_disjoint_packing_pair
    (hν : G.trianglePackingNumber ≤ 2)
    {e f : Finset V} (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hefCard : (e ∩ f).card = 0) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 4 := by
  classical
  have hefEmpty : e ∩ f = ∅ := Finset.card_eq_zero.mp hefCard
  have hef : Disjoint e f := Finset.disjoint_iff_inter_eq_empty.mpr hefEmpty
  let E : Finset (Finset V) :=
    G.triangles.filter fun q ↦ 2 ≤ (q ∩ e).card
  let F : Finset (Finset V) :=
    G.triangles.filter fun q ↦ 2 ≤ (q ∩ f).card
  have hEsub : E ⊆ G.triangles := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hFsub : F ⊆ G.triangles := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have heE : e ∈ E := by
    simp [E, he, G.card_eq_three_of_mem_triangles he]
  have hfF : f ∈ F := by
    simp [F, hf, G.card_eq_three_of_mem_triangles hf]
  have hEpair : ∀ ⦃q⦄, q ∈ E → ∀ ⦃r⦄, r ∈ E →
      2 ≤ (q ∩ r).card := by
    intro q hqE r hrE
    have hq := hEsub hqE
    have hr := hEsub hrE
    have hqe := (Finset.mem_filter.mp hqE).2
    have hre := (Finset.mem_filter.mp hrE).2
    have hqf := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hq) hef hqe
    have hrf := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hr) hef hre
    by_contra hqr
    have hqr' : (q ∩ r).card ≤ 1 := by omega
    have hpack := G.isTrianglePacking_triple hq hr hf hqr' hqf hrf
    have hpackCard := G.card_le_trianglePackingNumber hpack
    have hqfNe : q ≠ f := by
      intro h
      subst q
      have hfCard := G.card_eq_three_of_mem_triangles hf
      simp [hfCard] at hqf
    have hrfNe : r ≠ f := by
      intro h
      subst r
      have hfCard := G.card_eq_three_of_mem_triangles hf
      simp [hfCard] at hrf
    have hqrNe : q ≠ r := by
      intro h
      subst r
      have hqCard := G.card_eq_three_of_mem_triangles hq
      simp [hqCard] at hqr'
    have hcard : ({q, r, f} : Finset (Finset V)).card = 3 := by
      simp [hqfNe, hrfNe, hqrNe]
    omega
  have hFpair : ∀ ⦃q⦄, q ∈ F → ∀ ⦃r⦄, r ∈ F →
      2 ≤ (q ∩ r).card := by
    intro q hqF r hrF
    have hq := hFsub hqF
    have hr := hFsub hrF
    have hqfLarge := (Finset.mem_filter.mp hqF).2
    have hrfLarge := (Finset.mem_filter.mp hrF).2
    have hqe := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hq) hef.symm hqfLarge
    have hre := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hr) hef.symm hrfLarge
    by_contra hqr
    have hqr' : (q ∩ r).card ≤ 1 := by omega
    have hpack := G.isTrianglePacking_triple hq hr he hqr' hqe hre
    have hpackCard := G.card_le_trianglePackingNumber hpack
    have hqeNe : q ≠ e := by
      intro h
      subst q
      have heCard := G.card_eq_three_of_mem_triangles he
      simp [heCard] at hqe
    have hreNe : r ≠ e := by
      intro h
      subst r
      have heCard := G.card_eq_three_of_mem_triangles he
      simp [heCard] at hre
    have hqrNe : q ≠ r := by
      intro h
      subst r
      have hqCard := G.card_eq_three_of_mem_triangles hq
      simp [hqCard] at hqr'
    have hcard : ({q, r, e} : Finset (Finset V)).card = 3 := by
      simp [hqeNe, hreNe, hqrNe]
    omega
  obtain ⟨CE, hCE, hCEcard⟩ :=
    G.exists_two_family_transversal_of_pairwise_two_intersecting
      hEsub ⟨e, heE⟩ hEpair
  obtain ⟨CF, hCF, hCFcard⟩ :=
    G.exists_two_family_transversal_of_pairwise_two_intersecting
      hFsub ⟨f, hfF⟩ hFpair
  refine ⟨CE ∪ CF, ?_, ?_⟩
  · constructor
    · exact Finset.union_subset hCE.1 hCF.1
    · intro q hq
      by_cases hqE : q ∈ E
      · obtain ⟨d, hd, hdq⟩ := hCE.2 hqE
        exact ⟨d, Finset.mem_union_left CF hd, hdq⟩
      · by_cases hqF : q ∈ F
        · obtain ⟨d, hd, hdq⟩ := hCF.2 hqF
          exact ⟨d, Finset.mem_union_right CE hd, hdq⟩
        · have hqe : (q ∩ e).card ≤ 1 := by
            have hqE' := hqE
            simp only [E, Finset.mem_filter, hq, true_and, not_le] at hqE'
            omega
          have hqf : (q ∩ f).card ≤ 1 := by
            have hqF' := hqF
            simp only [F, Finset.mem_filter, hq, true_and, not_le] at hqF'
            omega
          have hpack := G.isTrianglePacking_triple he hf hq
            (by omega)
            (by simpa [Finset.inter_comm] using hqe)
            (by simpa [Finset.inter_comm] using hqf)
          have hpackCard := G.card_le_trianglePackingNumber hpack
          have hefNe : e ≠ f := by
            intro h
            subst f
            have heCard := G.card_eq_three_of_mem_triangles he
            simp [heCard] at hefCard
          have heqNe : e ≠ q := by
            intro h
            subst q
            have heCard := G.card_eq_three_of_mem_triangles he
            simp [heCard] at hqe
          have hfqNe : f ≠ q := by
            intro h
            subst q
            have hfCard := G.card_eq_three_of_mem_triangles hf
            simp [hfCard] at hqf
          have hcard : ({e, f, q} : Finset (Finset V)).card = 3 := by
            simp [hefNe, heqNe, hfqNe]
          omega
  · exact (Finset.card_union_le CE CF).trans (by omega)

/-- Parker's intersecting-packing case for packing number two. -/
theorem exists_four_transversal_of_one_intersection_packing_pair
    (hν : G.trianglePackingNumber ≤ 2)
    {e f : Finset V} (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hefCard : (e ∩ f).card = 1) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 4 := by
  classical
  obtain ⟨x, hef⟩ := Finset.card_eq_one.mp hefCard
  have hxe : x ∈ e := by
    have : x ∈ e ∩ f := by simp [hef]
    exact (Finset.mem_inter.mp this).1
  have hxf : x ∈ f := by
    have : x ∈ e ∩ f := by simp [hef]
    exact (Finset.mem_inter.mp this).2
  let P := G.privateTriangles e f
  have hPsub : P ⊆ G.triangles := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have heP : e ∈ P := by
    simp [P, privateTriangles, he,
      G.card_eq_three_of_mem_triangles he, hefCard]
  have hPpair : ∀ ⦃q⦄, q ∈ P → ∀ ⦃r⦄, r ∈ P →
      2 ≤ (q ∩ r).card := by
    simpa [P] using
      (G.privateTriangles_pairwise_two_intersecting hν (e := e) hf)
  by_cases hcommon :
      ∃ d ∈ e.powersetCard 2, ∀ ⦃q⦄, q ∈ P → d ⊆ q
  · obtain ⟨d, hd, hdcommon⟩ := hcommon
    let CP : Finset (Finset V) := {d}
    have hCP : G.IsTriangleFamilyTransversal P CP := by
      constructor
      · intro a ha
        simp only [CP, Finset.mem_singleton] at ha
        subst a
        have hddata := Finset.mem_powersetCard.mp hd
        exact G.mem_edges_of_subset_triangle he hddata.1 hddata.2
      · intro q hq
        exact ⟨d, by simp [CP], hdcommon hq⟩
    let TF := G.nearTriangles f
    have hTFsub : TF ⊆ G.triangles := by
      intro q hq
      exact (Finset.mem_filter.mp hq).1
    have hTFnear : ∀ ⦃q⦄, q ∈ TF → 2 ≤ (q ∩ f).card := by
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    have hCF := G.powersetCard_two_is_family_transversal hf hTFnear
    refine ⟨CP ∪ f.powersetCard 2, ?_, ?_⟩
    · constructor
      · exact Finset.union_subset hCP.1 hCF.1
      · intro q hq
        have hnear := G.near_one_of_packing_pair hν he hf hq (by omega)
        rcases hnear with hqe | hqf
        · by_cases hqf' : 2 ≤ (q ∩ f).card
          · obtain ⟨a, ha, haq⟩ := hCF.2
              (Finset.mem_filter.mpr ⟨hq, hqf'⟩)
            exact ⟨a, Finset.mem_union_right CP ha, haq⟩
          · have hqP : q ∈ P := Finset.mem_filter.mpr
              ⟨hq, hqe, by omega⟩
            obtain ⟨a, ha, haq⟩ := hCP.2 hqP
            exact ⟨a, Finset.mem_union_left _ ha, haq⟩
        · obtain ⟨a, ha, haq⟩ := hCF.2
            (Finset.mem_filter.mpr ⟨hq, hqf⟩)
          exact ⟨a, Finset.mem_union_right CP ha, haq⟩
    · have hCPcard : CP.card = 1 := by simp [CP]
      have hFcard := G.card_powersetCard_two_of_triangle hf
      exact (Finset.card_union_le CP (f.powersetCard 2)).trans (by omega)
  · have hPstructure :=
      G.family_common_pair_or_common_outside_vertex hPsub hPpair heP
    have htipData := Or.resolve_left hPstructure hcommon
    obtain ⟨v, hve, htip⟩ := htipData
    by_cases hall : ∀ ⦃q⦄, q ∈ P → x ∈ q
    · let TE := G.nearTriangles e
      have hTEsub : TE ⊆ G.triangles := by
        intro q hq
        exact (Finset.mem_filter.mp hq).1
      have hTEnear : ∀ ⦃q⦄, q ∈ TE → 2 ≤ (q ∩ e).card := by
        intro q hq
        exact (Finset.mem_filter.mp hq).2
      have hxTE : ∀ ⦃q⦄, q ∈ TE → x ∈ q := by
        intro q hqTE
        have hq := hTEsub hqTE
        have hqe := hTEnear hqTE
        by_cases hqf : (q ∩ f).card ≤ 1
        · exact hall (Finset.mem_filter.mpr ⟨hq, hqe, hqf⟩)
        · exact mem_common_of_two_large_intersections
            (G.card_eq_three_of_mem_triangles he)
            (G.card_eq_three_of_mem_triangles hf)
            (G.card_eq_three_of_mem_triangles hq) hef hqe (by omega)
      have hCE := G.pairsThrough_is_family_transversal he hxe hTEnear hxTE
      let Q := G.privateTriangles f e
      have hQsub : Q ⊆ G.triangles := by
        intro q hq
        exact (Finset.mem_filter.mp hq).1
      have hfQ : f ∈ Q := by
        simp [Q, privateTriangles, hf,
          G.card_eq_three_of_mem_triangles hf, Finset.inter_comm, hefCard]
      have hQpair : ∀ ⦃q⦄, q ∈ Q → ∀ ⦃r⦄, r ∈ Q →
          2 ≤ (q ∩ r).card := by
        simpa [Q] using
          (G.privateTriangles_pairwise_two_intersecting hν (e := f) he)
      obtain ⟨CQ, hCQ, hCQcard⟩ :=
        G.exists_two_family_transversal_of_pairwise_two_intersecting
          hQsub ⟨f, hfQ⟩ hQpair
      refine ⟨pairsThrough e x ∪ CQ, ?_, ?_⟩
      · constructor
        · exact Finset.union_subset hCE.1 hCQ.1
        · intro q hq
          have hnear := G.near_one_of_packing_pair hν he hf hq (by omega)
          rcases hnear with hqe | hqf
          · obtain ⟨a, ha, haq⟩ := hCE.2
              (Finset.mem_filter.mpr ⟨hq, hqe⟩)
            exact ⟨a, Finset.mem_union_left CQ ha, haq⟩
          · by_cases hqe' : 2 ≤ (q ∩ e).card
            · obtain ⟨a, ha, haq⟩ := hCE.2
                (Finset.mem_filter.mpr ⟨hq, hqe'⟩)
              exact ⟨a, Finset.mem_union_left CQ ha, haq⟩
            · have hqQ : q ∈ Q := Finset.mem_filter.mpr
                ⟨hq, hqf, by omega⟩
              obtain ⟨a, ha, haq⟩ := hCQ.2 hqQ
              exact ⟨a, Finset.mem_union_right _ ha, haq⟩
      · have hestar := card_pairsThrough_le_two
          (G.card_eq_three_of_mem_triangles he) hxe
        exact (Finset.card_union_le (pairsThrough e x) CQ).trans (by omega)
    · have hex : ∃ s ∈ P, x ∉ s := by
        by_contra h
        apply hall
        intro q hq
        by_contra hxq
        exact h ⟨q, hq, hxq⟩
      obtain ⟨s, hsP, hxs⟩ := hex
      have hsData := Finset.mem_filter.mp hsP
      have hs := hsData.1
      have hse : s ≠ e := by
        intro h
        subst s
        exact hxs hxe
      have hsvSet := htip hsP hse
      have hsvDiff : v ∈ s \ e := by
        rw [hsvSet]
        simp
      have hsv : v ∈ s := (Finset.mem_sdiff.mp hsvDiff).1
      have heraseCard : (e.erase x).card = 2 := by
        rw [Finset.card_erase_of_mem hxe,
          G.card_eq_three_of_mem_triangles he]
      have hedifference : e \ e.erase x = {x} := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_erase,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hze, hnot⟩
          by_contra hzx
          exact hnot ⟨hzx, hze⟩
        · rintro rfl
          exact ⟨hxe, by simp⟩
      have heraseSubset : e.erase x ⊆ s := by
        rcases subset_or_mem_of_large_trace heraseCard hedifference
            hsData.2.1 with hsub | hmem
        · exact hsub
        · exact (hxs hmem).elim
      have hsForm : s = insert v (e.erase x) := by
        have hsub : insert v (e.erase x) ⊆ s := by
          intro z hz
          simp only [Finset.mem_insert] at hz
          rcases hz with rfl | hz
          · exact hsv
          · exact heraseSubset hz
        apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
        have hvErase : v ∉ e.erase x := by
          intro h
          exact hve (Finset.mem_erase.mp h).2
        rw [Finset.card_insert_of_notMem hvErase, heraseCard,
          G.card_eq_three_of_mem_triangles hs]
      by_cases hvf : v ∈ f
      · apply (show False from ?_).elim
        apply hcommon
        refine ⟨e.erase x,
          Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, heraseCard⟩, ?_⟩
        intro q hqP
        by_cases hqe : q = e
        · subst q
          exact Finset.erase_subset _ _
        · have hvqDiff : v ∈ q \ e := by
            rw [htip hqP hqe]
            simp
          have hvq : v ∈ q := (Finset.mem_sdiff.mp hvqDiff).1
          have hqData := Finset.mem_filter.mp hqP
          have hxq : x ∉ q := by
            intro hxq
            have hxv : x ≠ v := by
              intro hxv
              exact hve (hxv ▸ hxe)
            have hpCard : ({x, v} : Finset V).card = 2 := by simp [hxv]
            have hpSub : {x, v} ⊆ q ∩ f := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨hxq, hxf⟩
              · exact Finset.mem_inter.mpr ⟨hvq, hvf⟩
            have := Finset.card_le_card hpSub
            omega
          rcases subset_or_mem_of_large_trace heraseCard hedifference
              hqData.2.1 with hsub | hmem
          · exact hsub
          · exact (hxq hmem).elim
      · have hdisj : Disjoint s f := by
          rw [Finset.disjoint_left]
          intro z hzs hzf
          rw [hsForm] at hzs
          simp only [Finset.mem_insert] at hzs
          rcases hzs with h | h
          · exact hvf (h ▸ hzf)
          · have hzef : z ∈ e ∩ f := Finset.mem_inter.mpr
                ⟨(Finset.mem_erase.mp h).2, hzf⟩
            have hzx : z = x := by simpa [hef] using hzef
            exact (Finset.mem_erase.mp h).1 hzx
        have hsfc : (s ∩ f).card = 0 := by
          rw [Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty.mp hdisj]
        exact G.exists_four_transversal_of_disjoint_packing_pair hν hs hf hsfc

/-- Tuza's inequality for graphs with triangle-packing number at most two. -/
theorem tuza_of_trianglePackingNumber_le_two
    (hν : G.trianglePackingNumber ≤ 2) :
    G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber := by
  classical
  by_cases hνone : G.trianglePackingNumber ≤ 1
  · exact G.tuza_of_trianglePackingNumber_le_one hνone
  · have hνeq : G.trianglePackingNumber = 2 := by omega
    obtain ⟨P, hP, hPcard⟩ := G.exists_max_trianglePacking
    rw [hνeq] at hPcard
    obtain ⟨e, f, hefNe, rfl⟩ := Finset.card_eq_two.mp hPcard
    have he : e ∈ G.triangles := hP.1 (by simp)
    have hf : f ∈ G.triangles := hP.1 (by simp)
    have hefLe : (e ∩ f).card ≤ 1 := hP.2 (by simp) (by simp) hefNe
    have hcover : ∃ C : Finset (Finset V),
        G.IsTriangleTransversal C ∧ C.card ≤ 4 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hefLe with hefZero | hefOne
      · exact G.exists_four_transversal_of_disjoint_packing_pair hν he hf hefZero
      · exact G.exists_four_transversal_of_one_intersection_packing_pair
          hν he hf hefOne
    obtain ⟨C, hC, hCcard⟩ := hcover
    have hτ := (G.triangleTransversalNumber_le_card hC).trans hCcard
    simpa [hνeq] using hτ

/-- Delete exactly those graph edges whose two endpoints both lie in `t`. -/
def deleteEdgesWithin (t : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬(u ∈ t ∧ v ∈ t)
  symm := by
    constructor
    intro u v huv
    exact ⟨G.symm.symm u v huv.1, by
      intro h
      exact huv.2 ⟨h.2, h.1⟩⟩
  loopless := by
    constructor
    intro u huu
    exact G.loopless.irrefl u huu.1

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem deleteEdgesWithin_adj {t : Finset V} {u v : V} :
    (G.deleteEdgesWithin t).Adj u v ↔
      G.Adj u v ∧ ¬(u ∈ t ∧ v ∈ t) := Iff.rfl

/-- The triangles remaining after deleting the edges internal to `t` are
exactly the original triangles that meet `t` in at most one vertex. -/
theorem mem_triangles_deleteEdgesWithin_iff
    {t q : Finset V} :
    q ∈ (G.deleteEdgesWithin t).triangles ↔
      q ∈ G.triangles ∧ (q ∩ t).card ≤ 1 := by
  classical
  constructor
  · intro hq
    have hq' : (G.deleteEdgesWithin t).IsNClique 3 q := by
      simpa [triangles] using hq
    have hqG : G.IsNClique 3 q := by
      refine ⟨?_, hq'.card_eq⟩
      intro u hu v hv huv
      exact (hq'.isClique hu hv huv).1
    refine ⟨by simpa [triangles] using hqG, ?_⟩
    by_contra hcard
    have htwo : 2 ≤ (q ∩ t).card := by omega
    obtain ⟨p, hpSub, hpCard⟩ :=
      Finset.exists_subset_card_eq (s := q ∩ t) (n := 2) htwo
    obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp hpCard
    subst p
    have hu : u ∈ q ∩ t := hpSub (by simp)
    have hv : v ∈ q ∩ t := hpSub (by simp)
    have hadj := hq'.isClique
      (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1 huv
    exact hadj.2 ⟨(Finset.mem_inter.mp hu).2,
      (Finset.mem_inter.mp hv).2⟩
  · rintro ⟨hq, hcard⟩
    have hq' : G.IsNClique 3 q := by simpa [triangles] using hq
    have hclique : (G.deleteEdgesWithin t).IsClique q := by
      intro u hu v hv huv
      refine ⟨hq'.isClique hu hv huv, ?_⟩
      rintro ⟨hut, hvt⟩
      have hpSub : ({u, v} : Finset V) ⊆ q ∩ t := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu, hut⟩
        · exact Finset.mem_inter.mpr ⟨hv, hvt⟩
      have hpCard : ({u, v} : Finset V).card = 2 := by simp [huv]
      have := Finset.card_le_card hpSub
      omega
    have hqDeleted : (G.deleteEdgesWithin t).IsNClique 3 q :=
      ⟨hclique, hq'.card_eq⟩
    simpa [triangles] using hqDeleted

/-- Every edge of `deleteEdgesWithin` is an edge of the original graph. -/
theorem edges_deleteEdgesWithin_subset {t : Finset V} :
    (G.deleteEdgesWithin t).edges ⊆ G.edges := by
  classical
  intro e he
  have he' : (G.deleteEdgesWithin t).IsNClique 2 e := by
    simpa [edges] using he
  have heG : G.IsNClique 2 e := by
    refine ⟨?_, he'.card_eq⟩
    intro u hu v hv huv
    exact (he'.isClique hu hv huv).1
  simpa [edges] using heG

/-- Inserting a triangle compatible with every member of a packing preserves
the packing property. -/
theorem isTrianglePacking_insert
    {P : Finset (Finset V)} {t : Finset V}
    (hP : G.IsTrianglePacking P) (ht : t ∈ G.triangles)
    (hcompat : ∀ ⦃q⦄, q ∈ P → (q ∩ t).card ≤ 1) :
    G.IsTrianglePacking (insert t P) := by
  classical
  constructor
  · intro q hq
    simp only [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact ht
    · exact hP.1 hq
  · intro q hq r hr hqr
    simp only [Finset.mem_insert] at hq hr
    rcases hq with rfl | hq <;> rcases hr with rfl | hr
    · exact (hqr rfl).elim
    · simpa [Finset.inter_comm] using hcompat hr
    · exact hcompat hq
    · exact hP.2 hq hr hqr

/-- Deleting the internal edges of a triangle in a graph of packing number
at most three leaves packing number at most two. -/
theorem trianglePackingNumber_deleteEdgesWithin_le_two
    (hν : G.trianglePackingNumber ≤ 3)
    {t : Finset V} (ht : t ∈ G.triangles) :
    (G.deleteEdgesWithin t).trianglePackingNumber ≤ 2 := by
  classical
  rw [(G.deleteEdgesWithin t).trianglePackingNumber_le_iff]
  intro P hP
  by_contra hcard
  have hPsubG : P ⊆ G.triangles := by
    intro q hq
    exact (G.mem_triangles_deleteEdgesWithin_iff.mp (hP.1 hq)).1
  have hPG : G.IsTrianglePacking P := ⟨hPsubG, hP.2⟩
  have hcompat : ∀ ⦃q⦄, q ∈ P → (q ∩ t).card ≤ 1 := by
    intro q hq
    exact (G.mem_triangles_deleteEdgesWithin_iff.mp (hP.1 hq)).2
  have htNot : t ∉ P := by
    intro htP
    have hsmall := hcompat htP
    have htCard := G.card_eq_three_of_mem_triangles ht
    simp [htCard] at hsmall
  have hinsert := G.isTrianglePacking_insert hPG ht hcompat
  have hbound := G.card_le_trianglePackingNumber hinsert
  rw [Finset.card_insert_of_notMem htNot] at hbound
  omega

/-- Parker's deletion step: a two-edge cover of all triangles near one
triangle in a maximum three-packing extends to a six-edge transversal. -/
theorem exists_six_transversal_of_two_cover_near_triangle
    (hν : G.trianglePackingNumber ≤ 3)
    {t : Finset V} (ht : t ∈ G.triangles)
    {C₀ : Finset (Finset V)}
    (hC₀ : G.IsTriangleFamilyTransversal (G.nearTriangles t) C₀)
    (hC₀card : C₀.card ≤ 2) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  let G' := G.deleteEdgesWithin t
  have hν' : G'.trianglePackingNumber ≤ 2 := by
    simpa [G'] using G.trianglePackingNumber_deleteEdgesWithin_le_two hν ht
  have htuza' := G'.tuza_of_trianglePackingNumber_le_two hν'
  obtain ⟨C₁, hC₁, hC₁eq⟩ := G'.exists_min_triangleTransversal
  have hC₁card : C₁.card ≤ 4 := by
    rw [hC₁eq]
    exact htuza'.trans (by omega)
  refine ⟨C₀ ∪ C₁, ?_, ?_⟩
  · constructor
    · exact Finset.union_subset hC₀.1
        (hC₁.1.trans (by simpa [G'] using G.edges_deleteEdgesWithin_subset (t := t)))
    · intro q hq
      by_cases hnear : 2 ≤ (q ∩ t).card
      · obtain ⟨e, he, heq⟩ := hC₀.2
          (Finset.mem_filter.mpr ⟨hq, hnear⟩)
        exact ⟨e, Finset.mem_union_left C₁ he, heq⟩
      · have hq' : q ∈ G'.triangles := by
          rw [G.mem_triangles_deleteEdgesWithin_iff]
          exact ⟨hq, by omega⟩
        obtain ⟨e, he, heq⟩ := hC₁.2 hq'
        exact ⟨e, Finset.mem_union_right C₀ he, heq⟩
  · exact (Finset.card_union_le C₀ C₁).trans (by omega)

end SimpleGraph
