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

omit [Fintype V] in
private theorem pair_subset_of_mem {u v : V} {s : Finset V}
    (hu : u ∈ s) (hv : v ∈ s) : ({u, v} : Finset V) ⊆ s := by
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with hwu | hwv
  · exact hwu ▸ hu
  · exact hwv ▸ hv

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

/-- Triangles close to `t` and to neither of two other packing members. -/
noncomputable def exclusiveTriangles
    (t e f : Finset V) : Finset (Finset V) := by
  classical
  exact G.triangles.filter fun q ↦
    2 ≤ (q ∩ t).card ∧ (q ∩ e).card ≤ 1 ∧ (q ∩ f).card ≤ 1

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

/-- Deleting the internal edges of a triangle lowers the packing number by
at least one. -/
theorem trianglePackingNumber_deleteEdgesWithin_add_one_le
    {t : Finset V} (ht : t ∈ G.triangles) :
    (G.deleteEdgesWithin t).trianglePackingNumber + 1 ≤
      G.trianglePackingNumber := by
  classical
  obtain ⟨P, hP, hPcard⟩ :=
    (G.deleteEdgesWithin t).exists_max_trianglePacking
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
  rw [Finset.card_insert_of_notMem htNot, hPcard] at hbound
  exact hbound

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

/-- Specialized form of Parker's Lemma 15 for a type-1a maximum packing.
If the triangles exclusive to `f` have a common pair and `f` is disjoint
from `g`, deleting the internal edges of `f` and `e` leaves a rank-one
graph. -/
theorem exists_six_transversal_of_common_exclusive_pair
    (hν : G.trianglePackingNumber ≤ 3)
    {e f g d : Finset V}
    (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (_hg : g ∈ G.triangles)
    (hef : (e ∩ f).card ≤ 1) (hfg : Disjoint f g)
    (hd : d ∈ f.powersetCard 2)
    (hdcommon : ∀ ⦃q⦄, q ∈ G.exclusiveTriangles f e g → d ⊆ q) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  let S := G.exclusiveTriangles f e g
  have hCS : G.IsTriangleFamilyTransversal S {d} := by
    constructor
    · intro a ha
      simp only [Finset.mem_singleton] at ha
      subst a
      have hddata := Finset.mem_powersetCard.mp hd
      exact G.mem_edges_of_subset_triangle hf hddata.1 hddata.2
    · intro q hq
      exact ⟨d, by simp, hdcommon hq⟩
  let G₁ := G.deleteEdgesWithin f
  have he₁ : e ∈ G₁.triangles := by
    rw [G.mem_triangles_deleteEdgesWithin_iff]
    exact ⟨he, by simpa [Finset.inter_comm] using hef⟩
  have hν₁ : G₁.trianglePackingNumber ≤ 2 := by
    have hdrop := G.trianglePackingNumber_deleteEdgesWithin_add_one_le hf
    have : (G.deleteEdgesWithin f).trianglePackingNumber ≤ 2 := by omega
    simpa [G₁] using this
  let G₂ := G₁.deleteEdgesWithin e
  have hν₂ : G₂.trianglePackingNumber ≤ 1 := by
    have hdrop := G₁.trianglePackingNumber_deleteEdgesWithin_add_one_le he₁
    have : (G₁.deleteEdgesWithin e).trianglePackingNumber ≤ 1 := by omega
    simpa [G₂] using this
  have htuza₂ := G₂.tuza_of_trianglePackingNumber_le_one hν₂
  obtain ⟨C₂, hC₂, hC₂eq⟩ := G₂.exists_min_triangleTransversal
  have hC₂card : C₂.card ≤ 2 := by
    rw [hC₂eq]
    exact htuza₂.trans (by omega)
  have hCE := G.powersetCard_two_is_family_transversal
    (F := G.nearTriangles e) he (by
      intro q hq
      exact (Finset.mem_filter.mp hq).2)
  let C : Finset (Finset V) := {d} ∪ e.powersetCard 2 ∪ C₂
  refine ⟨C, ?_, ?_⟩
  · constructor
    · intro a ha
      simp only [C, Finset.mem_union] at ha
      rcases ha with (ha | ha) | ha
      · exact hCS.1 ha
      · exact hCE.1 ha
      · have haG₂ : a ∈ G₂.edges := hC₂.1 ha
        have haG₁ : a ∈ G₁.edges :=
          (G₁.edges_deleteEdgesWithin_subset (t := e)) haG₂
        exact (G.edges_deleteEdgesWithin_subset (t := f)) haG₁
    · intro q hq
      by_cases hqe : 2 ≤ (q ∩ e).card
      · obtain ⟨a, ha, haq⟩ := hCE.2
          (Finset.mem_filter.mpr ⟨hq, hqe⟩)
        exact ⟨a, by simp [C, ha], haq⟩
      · by_cases hqf : 2 ≤ (q ∩ f).card
        · have hqg : (q ∩ g).card ≤ 1 :=
            card_inter_le_one_of_disjoint_of_large_inter
              (G.card_eq_three_of_mem_triangles hq) hfg hqf
          have hqS : q ∈ S := Finset.mem_filter.mpr
            ⟨hq, hqf, by omega, hqg⟩
          obtain ⟨a, ha, haq⟩ := hCS.2 hqS
          have had : a = d := by simpa using ha
          exact ⟨a, by simp [C, had], haq⟩
        · have hqG₁ : q ∈ G₁.triangles := by
            rw [G.mem_triangles_deleteEdgesWithin_iff]
            exact ⟨hq, by omega⟩
          have hqG₂ : q ∈ G₂.triangles := by
            rw [G₁.mem_triangles_deleteEdgesWithin_iff]
            exact ⟨hqG₁, by omega⟩
          obtain ⟨a, ha, haq⟩ := hC₂.2 hqG₂
          exact ⟨a, by simp [C, ha], haq⟩
  · have hEcard := G.card_powersetCard_two_of_triangle he
    have hsingle : ({d} : Finset (Finset V)).card = 1 := by simp
    have hunion₁ := Finset.card_union_le ({d} : Finset (Finset V))
      (e.powersetCard 2)
    have hunion₂ := Finset.card_union_le
      (({d} : Finset (Finset V)) ∪ e.powersetCard 2) C₂
    change (({d} : Finset (Finset V)) ∪ e.powersetCard 2 ∪ C₂).card ≤ 6
    omega

/-- A maximum three-packing with one member vertex-disjoint from the other
two has a six-edge transversal. -/
theorem exists_six_transversal_of_isolated_packing_member
    (hν : G.trianglePackingNumber ≤ 3)
    {t e f : Finset V}
    (ht : t ∈ G.triangles) (he : e ∈ G.triangles)
    (hf : f ∈ G.triangles)
    (hte : Disjoint t e) (htf : Disjoint t f)
    (hef : (e ∩ f).card ≤ 1) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  let T := G.nearTriangles t
  have hTsub : T ⊆ G.triangles := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have htT : t ∈ T := by
    simp [T, nearTriangles, ht, G.card_eq_three_of_mem_triangles ht]
  have hTpair : ∀ ⦃q⦄, q ∈ T → ∀ ⦃r⦄, r ∈ T →
      2 ≤ (q ∩ r).card := by
    intro q hqT r hrT
    have hq := hTsub hqT
    have hr := hTsub hrT
    have hqt := (Finset.mem_filter.mp hqT).2
    have hrt := (Finset.mem_filter.mp hrT).2
    have hqe := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hq) hte hqt
    have hqf := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hq) htf hqt
    have hre := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hr) hte hrt
    have hrf := card_inter_le_one_of_disjoint_of_large_inter
      (G.card_eq_three_of_mem_triangles hr) htf hrt
    by_contra hqr
    have hqr' : (q ∩ r).card ≤ 1 := by omega
    have hpack₃ := G.isTrianglePacking_triple hq hr he hqr' hqe hre
    have hpack₄ : G.IsTrianglePacking (insert f {q, r, e}) := by
      apply G.isTrianglePacking_insert hpack₃ hf
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hqf
      · exact hrf
      · exact hef
    have hbound := G.card_le_trianglePackingNumber hpack₄
    have hqrNe : q ≠ r := by
      intro h
      subst r
      have hqCard := G.card_eq_three_of_mem_triangles hq
      simp [hqCard] at hqr'
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
    have hfqNe : f ≠ q := by
      intro h
      subst q
      have hfCard := G.card_eq_three_of_mem_triangles hf
      simp [hfCard] at hqf
    have hfrNe : f ≠ r := by
      intro h
      subst r
      have hfCard := G.card_eq_three_of_mem_triangles hf
      simp [hfCard] at hrf
    have hfeNe : f ≠ e := by
      intro h
      subst f
      have heCard := G.card_eq_three_of_mem_triangles he
      simp [heCard] at hef
    have hcard₃ : ({q, r, e} : Finset (Finset V)).card = 3 := by
      simp [hqrNe, hqeNe, hreNe]
    have hfNot : f ∉ ({q, r, e} : Finset (Finset V)) := by
      simp [hfqNe, hfrNe, hfeNe]
    rw [Finset.card_insert_of_notMem hfNot, hcard₃] at hbound
    omega
  obtain ⟨C₀, hC₀, hC₀card⟩ :=
    G.exists_two_family_transversal_of_pairwise_two_intersecting
      hTsub ⟨t, htT⟩ hTpair
  exact G.exists_six_transversal_of_two_cover_near_triangle
    hν ht hC₀ hC₀card

/-- Maximality of a three-packing: every graph triangle shares an edge with
at least one packing member. -/
theorem near_one_of_packing_triple
    (hν : G.trianglePackingNumber ≤ 3)
    {e f g q : Finset V}
    (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hg : g ∈ G.triangles) (hq : q ∈ G.triangles)
    (hef : (e ∩ f).card ≤ 1) (heg : (e ∩ g).card ≤ 1)
    (hfg : (f ∩ g).card ≤ 1) :
    2 ≤ (q ∩ e).card ∨ 2 ≤ (q ∩ f).card ∨ 2 ≤ (q ∩ g).card := by
  classical
  by_contra h
  push Not at h
  have hqe : (q ∩ e).card ≤ 1 := by omega
  have hqf : (q ∩ f).card ≤ 1 := by omega
  have hqg : (q ∩ g).card ≤ 1 := by omega
  have hpack₃ := G.isTrianglePacking_triple he hf hg hef heg hfg
  have hpack₄ : G.IsTrianglePacking (insert q {e, f, g}) := by
    apply G.isTrianglePacking_insert hpack₃ hq
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simpa [Finset.inter_comm] using hqe
    · simpa [Finset.inter_comm] using hqf
    · simpa [Finset.inter_comm] using hqg
  have hbound := G.card_le_trianglePackingNumber hpack₄
  have hefNe : e ≠ f := by
    intro h
    subst f
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at hef
  have hegNe : e ≠ g := by
    intro h
    subst g
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at heg
  have hfgNe : f ≠ g := by
    intro h
    subst g
    have hfCard := G.card_eq_three_of_mem_triangles hf
    simp [hfCard] at hfg
  have hqeNe : q ≠ e := by
    intro h
    subst q
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at hqe
  have hqfNe : q ≠ f := by
    intro h
    subst q
    have hfCard := G.card_eq_three_of_mem_triangles hf
    simp [hfCard] at hqf
  have hqgNe : q ≠ g := by
    intro h
    subst q
    have hgCard := G.card_eq_three_of_mem_triangles hg
    simp [hgCard] at hqg
  have hcard₃ : ({e, f, g} : Finset (Finset V)).card = 3 := by
    simp [hefNe, hegNe, hfgNe]
  have hqNot : q ∉ ({e, f, g} : Finset (Finset V)) := by
    simp [hqeNe, hqfNe, hqgNe]
  rw [Finset.card_insert_of_notMem hqNot, hcard₃] at hbound
  omega

/-- An exclusive family associated with one member of a maximum
three-packing is pairwise two-intersecting. -/
theorem exclusiveTriangles_pairwise_two_intersecting
    (hν : G.trianglePackingNumber ≤ 3)
    {t e f : Finset V} (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hef : (e ∩ f).card ≤ 1) :
    ∀ ⦃q⦄, q ∈ G.exclusiveTriangles t e f →
      ∀ ⦃r⦄, r ∈ G.exclusiveTriangles t e f → 2 ≤ (q ∩ r).card := by
  classical
  intro q hqS r hrS
  have hqData := Finset.mem_filter.mp hqS
  have hrData := Finset.mem_filter.mp hrS
  by_contra hqr
  have hqr' : (q ∩ r).card ≤ 1 := by omega
  have hpack₃ := G.isTrianglePacking_triple
    hqData.1 hrData.1 he hqr' hqData.2.2.1 hrData.2.2.1
  have hpack₄ : G.IsTrianglePacking (insert f {q, r, e}) := by
    apply G.isTrianglePacking_insert hpack₃ hf
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hqData.2.2.2
    · exact hrData.2.2.2
    · exact hef
  have hbound := G.card_le_trianglePackingNumber hpack₄
  have hqrNe : q ≠ r := by
    intro h
    subst r
    have hqCard := G.card_eq_three_of_mem_triangles hqData.1
    simp [hqCard] at hqr'
  have hqeNe : q ≠ e := by
    intro h
    subst q
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at hqData
  have hreNe : r ≠ e := by
    intro h
    subst r
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at hrData
  have hfqNe : f ≠ q := by
    intro h
    subst q
    have hfCard := G.card_eq_three_of_mem_triangles hf
    simp [hfCard] at hqData
  have hfrNe : f ≠ r := by
    intro h
    subst r
    have hfCard := G.card_eq_three_of_mem_triangles hf
    simp [hfCard] at hrData
  have hfeNe : f ≠ e := by
    intro h
    subst f
    have heCard := G.card_eq_three_of_mem_triangles he
    simp [heCard] at hef
  have hcard₃ : ({q, r, e} : Finset (Finset V)).card = 3 := by
    simp [hqrNe, hqeNe, hreNe]
  have hfNot : f ∉ ({q, r, e} : Finset (Finset V)) := by
    simp [hfqNe, hfrNe, hfeNe]
  rw [Finset.card_insert_of_notMem hfNot, hcard₃] at hbound
  omega

omit [Fintype V] in
theorem exists_eq_insert_of_subset_card_two_card_three
    {A q : Finset V} (hA : A.card = 2) (hq : q.card = 3)
    (hsub : A ⊆ q) :
    ∃ u ∉ A, q = insert u A := by
  classical
  have hdiffCard : (q \ A).card = 1 := by
    rw [Finset.card_sdiff]
    have hinter : A ∩ q = A := Finset.inter_eq_left.mpr hsub
    rw [hinter, hq, hA]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hdiffCard
  have huDiff : u ∈ q \ A := by simp [hu]
  refine ⟨u, (Finset.mem_sdiff.mp huDiff).2, ?_⟩
  ext z
  constructor
  · intro hzq
    by_cases hzA : z ∈ A
    · exact Finset.mem_insert_of_mem hzA
    · have : z ∈ q \ A := Finset.mem_sdiff.mpr ⟨hzq, hzA⟩
      have hzu : z = u := by simpa [hu] using this
      exact hzu ▸ Finset.mem_insert_self u A
  · intro hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact (Finset.mem_sdiff.mp huDiff).1
    · exact hsub hz

omit [Fintype V] in
theorem sdiff_erase_eq_singleton {t : Finset V} {x : V} (hx : x ∈ t) :
    t \ t.erase x = {x} := by
  classical
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hzt, hnot⟩
    by_contra hzx
    exact hnot ⟨hzx, hzt⟩
  · rintro rfl
    exact ⟨hx, by simp⟩

omit [Fintype V] in
theorem card_inter_insert_le_one_of_disjoint
    {A t : Finset V} {u : V} (hdisj : Disjoint A t) :
    (insert u A ∩ t).card ≤ 1 := by
  classical
  have hsub : insert u A ∩ t ⊆ {u} := by
    intro z hz
    have hzInsert := (Finset.mem_inter.mp hz).1
    simp only [Finset.mem_insert] at hzInsert
    rcases hzInsert with rfl | hzA
    · simp
    · exact (Finset.disjoint_left.mp hdisj hzA
        (Finset.mem_inter.mp hz).2).elim
  exact (Finset.card_le_card hsub).trans (by simp)

omit [Fintype V] in
theorem eq_of_inter_eq_and_sdiff_eq
    {q r t : Finset V} (hi : q ∩ t = r ∩ t)
    (hd : q \ t = r \ t) : q = r := by
  classical
  ext z
  by_cases hzt : z ∈ t
  · have hqi : z ∈ q ↔ z ∈ q ∩ t := by simp [hzt]
    have hri : z ∈ r ↔ z ∈ r ∩ t := by simp [hzt]
    exact hqi.trans ((Finset.ext_iff.mp hi z).trans hri.symm)
  · have hqd : z ∈ q ↔ z ∈ q \ t := by simp [hzt]
    have hrd : z ∈ r ↔ z ∈ r \ t := by simp [hzt]
    exact hqd.trans ((Finset.ext_iff.mp hd z).trans hrd.symm)

/-- If the pair of vertices of `t` opposite `x` has no extension other than
`t`, the two pairs of `t` through `x` cover every triangle near `t`. -/
theorem exists_six_transversal_of_no_opposite_pair_extension
    (hν : G.trianglePackingNumber ≤ 3)
    {t : Finset V} {x : V} (ht : t ∈ G.triangles) (hx : x ∈ t)
    (hunique : ∀ ⦃q⦄, q ∈ G.triangles → t.erase x ⊆ q → q = t) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  let T := G.nearTriangles t
  have hTnear : ∀ ⦃q⦄, q ∈ T → 2 ≤ (q ∩ t).card := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hxall : ∀ ⦃q⦄, q ∈ T → x ∈ q := by
    intro q hqT
    have hq := (Finset.mem_filter.mp hqT).1
    have htEraseCard : (t.erase x).card = 2 := by
      rw [Finset.card_erase_of_mem hx,
        G.card_eq_three_of_mem_triangles ht]
    rcases subset_or_mem_of_large_trace htEraseCard
        (sdiff_erase_eq_singleton hx) (hTnear hqT) with hsub | hxq
    · rw [hunique hq hsub]
      exact hx
    · exact hxq
  have hCT := G.pairsThrough_is_family_transversal ht hx hTnear hxall
  have hcard := card_pairsThrough_le_two
    (G.card_eq_three_of_mem_triangles ht) hx
  exact G.exists_six_transversal_of_two_cover_near_triangle
    hν ht hCT hcard

/-- Parker's type-1a case: the middle member meets two vertex-disjoint
packing members in distinct vertices. -/
theorem exists_six_transversal_of_type_one_a
    (hν : G.trianglePackingNumber ≤ 3)
    {e f g : Finset V} {x y : V}
    (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hg : g ∈ G.triangles)
    (hefSet : e ∩ f = {x}) (hegSet : e ∩ g = {y})
    (hfg : Disjoint f g) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  have hefCard : (e ∩ f).card = 1 := by simp [hefSet]
  have hegCard : (e ∩ g).card = 1 := by simp [hegSet]
  have hfgCard : (f ∩ g).card = 0 := by
    rw [Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty.mp hfg]
  have hxe : x ∈ e := by
    have : x ∈ e ∩ f := by simp [hefSet]
    exact (Finset.mem_inter.mp this).1
  have hxf : x ∈ f := by
    have : x ∈ e ∩ f := by simp [hefSet]
    exact (Finset.mem_inter.mp this).2
  have hye : y ∈ e := by
    have : y ∈ e ∩ g := by simp [hegSet]
    exact (Finset.mem_inter.mp this).1
  have hyg : y ∈ g := by
    have : y ∈ e ∩ g := by simp [hegSet]
    exact (Finset.mem_inter.mp this).2
  have hxy : x ≠ y := by
    intro hxy
    subst y
    exact (Finset.disjoint_left.mp hfg) hxf hyg
  let A := f.erase x
  let B := g.erase y
  have hAcard : A.card = 2 := by
    change (f.erase x).card = 2
    rw [Finset.card_erase_of_mem hxf,
      G.card_eq_three_of_mem_triangles hf]
  have hBcard : B.card = 2 := by
    change (g.erase y).card = 2
    rw [Finset.card_erase_of_mem hyg,
      G.card_eq_three_of_mem_triangles hg]
  have hfForm : f = insert x A := by
    simpa [A] using (Finset.insert_erase hxf).symm
  have hgForm : g = insert y B := by
    simpa [B] using (Finset.insert_erase hyg).symm
  have hAf : A ⊆ f := by exact Finset.erase_subset _ _
  have hBg : B ⊆ g := by exact Finset.erase_subset _ _
  have hAdisjE : Disjoint A e := by
    rw [Finset.disjoint_left]
    intro z hzA hze
    have hzef : z ∈ e ∩ f := Finset.mem_inter.mpr ⟨hze, hAf hzA⟩
    have hzx : z = x := by simpa [hefSet] using hzef
    exact (Finset.mem_erase.mp hzA).1 hzx
  have hAdisjG : Disjoint A g := by
    rw [Finset.disjoint_left]
    intro z hzA hzg
    exact (Finset.disjoint_left.mp hfg) (hAf hzA) hzg
  have hBdisjE : Disjoint B e := by
    rw [Finset.disjoint_left]
    intro z hzB hze
    have hzeg : z ∈ e ∩ g := Finset.mem_inter.mpr ⟨hze, hBg hzB⟩
    have hzy : z = y := by simpa [hegSet] using hzeg
    exact (Finset.mem_erase.mp hzB).1 hzy
  have hBdisjF : Disjoint B f := by
    rw [Finset.disjoint_left]
    intro z hzB hzf
    exact (Finset.disjoint_left.mp hfg) hzf (hBg hzB)
  by_cases hExtF : ∃ q ∈ G.triangles, A ⊆ q ∧ q ≠ f
  · obtain ⟨f₁, hf₁, hAf₁, hf₁f⟩ := hExtF
    obtain ⟨u, huA, hf₁Form⟩ :=
      exists_eq_insert_of_subset_card_two_card_three hAcard
        (G.card_eq_three_of_mem_triangles hf₁) hAf₁
    have hux : u ≠ x := by
      intro hux
      subst u
      apply hf₁f
      rw [hf₁Form]
      exact hfForm.symm
    have huf : u ∉ f := by
      rw [hfForm]
      simp [huA, hux]
    by_cases hExtG : ∃ q ∈ G.triangles, B ⊆ q ∧ q ≠ g
    · obtain ⟨g₁, hg₁, hBg₁, hg₁g⟩ := hExtG
      obtain ⟨v, hvB, hg₁Form⟩ :=
        exists_eq_insert_of_subset_card_two_card_three hBcard
          (G.card_eq_three_of_mem_triangles hg₁) hBg₁
      have hvy : v ≠ y := by
        intro hvy
        subst v
        apply hg₁g
        rw [hg₁Form]
        exact hgForm.symm
      have hvg : v ∉ g := by
        rw [hgForm]
        simp [hvB, hvy]
      by_cases huLoc : u ∈ (e ∪ g) \ {x}
      · by_cases hvLoc : v ∈ (e ∪ f) \ {y}
        · let SF := G.exclusiveTriangles f e g
          let SG := G.exclusiveTriangles g e f
          have hfSF : f ∈ SF := by
            simp [SF, exclusiveTriangles, hf,
              G.card_eq_three_of_mem_triangles hf,
              Finset.inter_comm, hefCard, hfgCard]
          have hgSG : g ∈ SG := by
            simp [SG, exclusiveTriangles, hg,
              G.card_eq_three_of_mem_triangles hg,
              Finset.inter_comm, hegCard, hfgCard]
          have hf₁SF : f₁ ∈ SF := by
            have hf₁e : (f₁ ∩ e).card ≤ 1 := by
              rw [hf₁Form]
              exact card_inter_insert_le_one_of_disjoint hAdisjE
            have hf₁g : (f₁ ∩ g).card ≤ 1 := by
              rw [hf₁Form]
              exact card_inter_insert_le_one_of_disjoint hAdisjG
            have hnear : 2 ≤ (f₁ ∩ f).card := by
              have hsub : A ⊆ f₁ ∩ f := fun z hz ↦
                Finset.mem_inter.mpr ⟨hAf₁ hz, hAf hz⟩
              have := Finset.card_le_card hsub
              omega
            exact Finset.mem_filter.mpr ⟨hf₁, hnear, hf₁e, hf₁g⟩
          have hg₁SG : g₁ ∈ SG := by
            have hg₁e : (g₁ ∩ e).card ≤ 1 := by
              rw [hg₁Form]
              exact card_inter_insert_le_one_of_disjoint hBdisjE
            have hg₁f : (g₁ ∩ f).card ≤ 1 := by
              rw [hg₁Form]
              exact card_inter_insert_le_one_of_disjoint hBdisjF
            have hnear : 2 ≤ (g₁ ∩ g).card := by
              have hsub : B ⊆ g₁ ∩ g := fun z hz ↦
                Finset.mem_inter.mpr ⟨hBg₁ hz, hBg hz⟩
              have := Finset.card_le_card hsub
              omega
            exact Finset.mem_filter.mpr ⟨hg₁, hnear, hg₁e, hg₁f⟩
          have hSFsub : SF ⊆ G.triangles := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hSGsub : SG ⊆ G.triangles := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hSFpair : ∀ ⦃q⦄, q ∈ SF → ∀ ⦃r⦄, r ∈ SF →
              2 ≤ (q ∩ r).card := by
            simpa [SF] using
              (G.exclusiveTriangles_pairwise_two_intersecting hν he hg
                (by omega) (t := f))
          have hSGpair : ∀ ⦃q⦄, q ∈ SG → ∀ ⦃r⦄, r ∈ SG →
              2 ≤ (q ∩ r).card := by
            simpa [SG] using
              (G.exclusiveTriangles_pairwise_two_intersecting hν he hf
                (by omega) (t := g))
          by_cases hcommonF :
              ∃ d ∈ f.powersetCard 2, ∀ ⦃q⦄, q ∈ SF → d ⊆ q
          · obtain ⟨d, hd, hdcommon⟩ := hcommonF
            exact G.exists_six_transversal_of_common_exclusive_pair
              hν he hf hg (by omega) hfg hd (by simpa [SF] using hdcommon)
          · by_cases hcommonG :
                ∃ d ∈ g.powersetCard 2, ∀ ⦃q⦄, q ∈ SG → d ⊆ q
            · obtain ⟨d, hd, hdcommon⟩ := hcommonG
              exact G.exists_six_transversal_of_common_exclusive_pair
                hν he hg hf (by omega) hfg.symm hd
                (by simpa [SG] using hdcommon)
            · have hSFstructure :=
                G.family_common_pair_or_common_outside_vertex
                  hSFsub hSFpair hfSF
              obtain ⟨w, hwf, htipF₀⟩ :=
                Or.resolve_left hSFstructure hcommonF
              have hf₁Diff : f₁ \ f = {u} := by
                ext z
                constructor
                · intro hz
                  have hzf₁ := (Finset.mem_sdiff.mp hz).1
                  rw [hf₁Form] at hzf₁
                  simp only [Finset.mem_insert] at hzf₁
                  rcases hzf₁ with rfl | hzA
                  · simp
                  · exact ((Finset.mem_sdiff.mp hz).2 (hAf hzA)).elim
                · intro hz
                  have hzu : z = u := by simpa using hz
                  subst z
                  exact Finset.mem_sdiff.mpr ⟨by simp [hf₁Form], huf⟩
              have hwu : w = u := by
                have hw := htipF₀ hf₁SF hf₁f
                rw [hf₁Diff] at hw
                exact Finset.singleton_inj.mp hw.symm
              subst w
              have hSGstructure :=
                G.family_common_pair_or_common_outside_vertex
                  hSGsub hSGpair hgSG
              obtain ⟨w, hwg, htipG₀⟩ :=
                Or.resolve_left hSGstructure hcommonG
              have hg₁Diff : g₁ \ g = {v} := by
                ext z
                constructor
                · intro hz
                  have hzg₁ := (Finset.mem_sdiff.mp hz).1
                  rw [hg₁Form] at hzg₁
                  simp only [Finset.mem_insert] at hzg₁
                  rcases hzg₁ with rfl | hzB
                  · simp
                  · exact ((Finset.mem_sdiff.mp hz).2 (hBg hzB)).elim
                · intro hz
                  have hzv : z = v := by simpa using hz
                  subst z
                  exact Finset.mem_sdiff.mpr ⟨by simp [hg₁Form], hvg⟩
              have hwv : w = v := by
                have hw := htipG₀ hg₁SG hg₁g
                rw [hg₁Diff] at hw
                exact Finset.singleton_inj.mp hw.symm
              subst w
              have hf₂Exists : ∃ q ∈ SF, q ≠ f ∧ q ≠ f₁ := by
                by_contra h
                apply hcommonF
                refine ⟨A, Finset.mem_powersetCard.mpr ⟨hAf, hAcard⟩, ?_⟩
                intro q hq
                by_cases hqf : q = f
                · subst q
                  exact hAf
                · by_cases hqf₁ : q = f₁
                  · subst q
                    exact hAf₁
                  · exact (h ⟨q, hq, hqf, hqf₁⟩).elim
              obtain ⟨f₂, hf₂SF, hf₂f, hf₂f₁⟩ := hf₂Exists
              have hg₂Exists : ∃ q ∈ SG, q ≠ g ∧ q ≠ g₁ := by
                by_contra h
                apply hcommonG
                refine ⟨B, Finset.mem_powersetCard.mpr ⟨hBg, hBcard⟩, ?_⟩
                intro q hq
                by_cases hqg : q = g
                · subst q
                  exact hBg
                · by_cases hqg₁ : q = g₁
                  · subst q
                    exact hBg₁
                  · exact (h ⟨q, hq, hqg, hqg₁⟩).elim
              obtain ⟨g₂, hg₂SG, hg₂g, hg₂g₁⟩ := hg₂Exists
              have htipF : ∀ ⦃q⦄, q ∈ SF → q ≠ f → q \ f = {u} := htipF₀
              have htipG : ∀ ⦃q⦄, q ∈ SG → q ≠ g → q \ g = {v} := htipG₀
              have hf₁Inter : f₁ ∩ f = A := by
                ext z
                rw [hf₁Form]
                simp only [Finset.mem_inter, Finset.mem_insert]
                constructor
                · rintro ⟨rfl | hzA, hzf⟩
                  · exact (huf hzf).elim
                  · exact hzA
                · intro hzA
                  exact ⟨Or.inr hzA, hAf hzA⟩
              have hg₁Inter : g₁ ∩ g = B := by
                ext z
                rw [hg₁Form]
                simp only [Finset.mem_inter, Finset.mem_insert]
                constructor
                · rintro ⟨rfl | hzB, hzg⟩
                  · exact (hvg hzg).elim
                  · exact hzB
                · intro hzB
                  exact ⟨Or.inr hzB, hBg hzB⟩
              have hf₂Data := Finset.mem_filter.mp hf₂SF
              have hg₂Data := Finset.mem_filter.mp hg₂SG
              have hf₂TraceCard := card_inter_eq_two_of_card_eq_three
                (G.card_eq_three_of_mem_triangles hf₂Data.1)
                (G.card_eq_three_of_mem_triangles hf) hf₂f hf₂Data.2.1
              have hg₂TraceCard := card_inter_eq_two_of_card_eq_three
                (G.card_eq_three_of_mem_triangles hg₂Data.1)
                (G.card_eq_three_of_mem_triangles hg) hg₂g hg₂Data.2.1
              have hf₂TraceNe : f₂ ∩ f ≠ A := by
                intro htrace
                apply hf₂f₁
                exact eq_of_inter_eq_and_sdiff_eq
                  (htrace.trans hf₁Inter.symm)
                  ((htipF hf₂SF hf₂f).trans hf₁Diff.symm)
              have hg₂TraceNe : g₂ ∩ g ≠ B := by
                intro htrace
                apply hg₂g₁
                exact eq_of_inter_eq_and_sdiff_eq
                  (htrace.trans hg₁Inter.symm)
                  ((htipG hg₂SG hg₂g).trans hg₁Diff.symm)
              have hxf₂ : x ∈ f₂ := by
                rcases subset_or_mem_of_large_trace hAcard
                    (sdiff_erase_eq_singleton hxf) hf₂Data.2.1 with hsub | hxmem
                · have hsub' : A ⊆ f₂ ∩ f := fun z hz ↦
                    Finset.mem_inter.mpr ⟨hsub hz, hAf hz⟩
                  have heq : A = f₂ ∩ f :=
                    Finset.eq_of_subset_of_card_le hsub' (by omega)
                  exact (hf₂TraceNe heq.symm).elim
                · exact hxmem
              have hyg₂ : y ∈ g₂ := by
                rcases subset_or_mem_of_large_trace hBcard
                    (sdiff_erase_eq_singleton hyg) hg₂Data.2.1 with hsub | hymem
                · have hsub' : B ⊆ g₂ ∩ g := fun z hz ↦
                    Finset.mem_inter.mpr ⟨hsub hz, hBg hz⟩
                  have heq : B = g₂ ∩ g :=
                    Finset.eq_of_subset_of_card_le hsub' (by omega)
                  exact (hg₂TraceNe heq.symm).elim
                · exact hymem
              have huf₂ : u ∈ f₂ := by
                have : u ∈ f₂ \ f := by rw [htipF hf₂SF hf₂f]; simp
                exact (Finset.mem_sdiff.mp this).1
              have hvg₂ : v ∈ g₂ := by
                have : v ∈ g₂ \ g := by rw [htipG hg₂SG hg₂g]; simp
                exact (Finset.mem_sdiff.mp this).1
              have hue : u ∉ e := by
                intro hue
                have hxu : x ≠ u := by
                  intro h
                  exact huf (h ▸ hxf)
                have hpSub : ({x, u} : Finset V) ⊆ f₂ ∩ e := by
                  intro z hz
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with rfl | rfl
                  · exact Finset.mem_inter.mpr ⟨hxf₂, hxe⟩
                  · exact Finset.mem_inter.mpr ⟨huf₂, hue⟩
                have hpCard : ({x, u} : Finset V).card = 2 := by simp [hxu]
                have := Finset.card_le_card hpSub
                omega
              have hve : v ∉ e := by
                intro hve
                have hyv : y ≠ v := by
                  intro h
                  exact hvg (h ▸ hyg)
                have hpSub : ({y, v} : Finset V) ⊆ g₂ ∩ e := by
                  intro z hz
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with rfl | rfl
                  · exact Finset.mem_inter.mpr ⟨hyg₂, hye⟩
                  · exact Finset.mem_inter.mpr ⟨hvg₂, hve⟩
                have hpCard : ({y, v} : Finset V).card = 2 := by simp [hyv]
                have := Finset.card_le_card hpSub
                omega
              have hug : u ∈ g := by
                have huUnion := (Finset.mem_sdiff.mp huLoc).1
                rcases Finset.mem_union.mp huUnion with hue' | hug
                · exact (hue hue').elim
                · exact hug
              have hvf : v ∈ f := by
                have hvUnion := (Finset.mem_sdiff.mp hvLoc).1
                rcases Finset.mem_union.mp hvUnion with hve' | hvf
                · exact (hve hve').elim
                · exact hvf
              have huv : u ≠ v := by
                intro huv
                subst v
                exact (Finset.disjoint_left.mp hfg) hvf hug
              let R : Finset (Finset V) :=
                e.powersetCard 2 ∪ {{u, v}, f.erase v, g.erase u}
              let C : Finset (Finset V) := R ∩ G.edges
              have hRcard : R.card ≤ 6 := by
                have hEcard := G.card_powersetCard_two_of_triangle he
                have hthree : ({{u, v}, f.erase v, g.erase u} :
                    Finset (Finset V)).card ≤ 3 := Finset.card_le_three
                change (e.powersetCard 2 ∪
                  ({{u, v}, f.erase v, g.erase u} :
                    Finset (Finset V))).card ≤ 6
                calc
                  _ ≤ (e.powersetCard 2).card +
                      ({{u, v}, f.erase v, g.erase u} :
                        Finset (Finset V)).card := Finset.card_union_le _ _
                  _ ≤ 3 + 3 := Nat.add_le_add hEcard.le hthree
                  _ = 6 := rfl
              refine ⟨C, ?_, ?_⟩
              · constructor
                · exact Finset.inter_subset_right
                · intro q hq
                  have hnear := G.near_one_of_packing_triple hν he hf hg hq
                    (by omega) (by omega) (by omega)
                  rcases hnear with hqe | hqf | hqg
                  · obtain ⟨p, hp, hpCard⟩ :=
                      Finset.exists_subset_card_eq (s := q ∩ e) (n := 2) hqe
                    have hpE : p ∈ e.powersetCard 2 :=
                      Finset.mem_powersetCard.mpr
                        ⟨hp.trans Finset.inter_subset_right, hpCard⟩
                    have hpq : p ⊆ q := hp.trans Finset.inter_subset_left
                    have hpEdge := G.mem_edges_of_subset_triangle hq hpq hpCard
                    exact ⟨p, Finset.mem_inter.mpr
                      ⟨Finset.mem_union_left _ hpE, hpEdge⟩, hpq⟩
                  · by_cases hqe' : 2 ≤ (q ∩ e).card
                    · obtain ⟨p, hp, hpCard⟩ :=
                        Finset.exists_subset_card_eq (s := q ∩ e) (n := 2) hqe'
                      have hpE : p ∈ e.powersetCard 2 :=
                        Finset.mem_powersetCard.mpr
                          ⟨hp.trans Finset.inter_subset_right, hpCard⟩
                      have hpq : p ⊆ q := hp.trans Finset.inter_subset_left
                      have hpEdge := G.mem_edges_of_subset_triangle hq hpq hpCard
                      exact ⟨p, Finset.mem_inter.mpr
                        ⟨Finset.mem_union_left _ hpE, hpEdge⟩, hpq⟩
                    · have hqg' : (q ∩ g).card ≤ 1 :=
                        card_inter_le_one_of_disjoint_of_large_inter
                          (G.card_eq_three_of_mem_triangles hq) hfg hqf
                      have hqSF : q ∈ SF := Finset.mem_filter.mpr
                        ⟨hq, hqf, by omega, hqg'⟩
                      by_cases hqRoot : q = f
                      · subst q
                        have hpCard : (f.erase v).card = 2 := by
                          rw [Finset.card_erase_of_mem hvf,
                            G.card_eq_three_of_mem_triangles hf]
                        have hpEdge := G.mem_edges_of_subset_triangle hf
                          (Finset.erase_subset _ _) hpCard
                        exact ⟨f.erase v, Finset.mem_inter.mpr
                          ⟨by simp [R], hpEdge⟩, Finset.erase_subset _ _⟩
                      · have huq : u ∈ q := by
                          have : u ∈ q \ f := by rw [htipF hqSF hqRoot]; simp
                          exact (Finset.mem_sdiff.mp this).1
                        have hEraseCard : (f.erase v).card = 2 := by
                          rw [Finset.card_erase_of_mem hvf,
                            G.card_eq_three_of_mem_triangles hf]
                        rcases subset_or_mem_of_large_trace hEraseCard
                            (sdiff_erase_eq_singleton hvf) hqf with hsub | hvq
                        · have hpEdge := G.mem_edges_of_subset_triangle hq hsub hEraseCard
                          exact ⟨f.erase v, Finset.mem_inter.mpr
                            ⟨by simp [R], hpEdge⟩, hsub⟩
                        · have hpSub : {u, v} ⊆ q := by
                            intro z hz
                            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                            exact hz.elim (fun h ↦ h ▸ huq) (fun h ↦ h ▸ hvq)
                          have hpCard : ({u, v} : Finset V).card = 2 := by simp [huv]
                          have hpEdge := G.mem_edges_of_subset_triangle hq hpSub hpCard
                          exact ⟨{u, v}, Finset.mem_inter.mpr
                            ⟨by simp [R], hpEdge⟩, hpSub⟩
                  · by_cases hqe' : 2 ≤ (q ∩ e).card
                    · obtain ⟨p, hp, hpCard⟩ :=
                        Finset.exists_subset_card_eq (s := q ∩ e) (n := 2) hqe'
                      have hpE : p ∈ e.powersetCard 2 :=
                        Finset.mem_powersetCard.mpr
                          ⟨hp.trans Finset.inter_subset_right, hpCard⟩
                      have hpq : p ⊆ q := hp.trans Finset.inter_subset_left
                      have hpEdge := G.mem_edges_of_subset_triangle hq hpq hpCard
                      exact ⟨p, Finset.mem_inter.mpr
                        ⟨Finset.mem_union_left _ hpE, hpEdge⟩, hpq⟩
                    · have hqf' : (q ∩ f).card ≤ 1 :=
                        card_inter_le_one_of_disjoint_of_large_inter
                          (G.card_eq_three_of_mem_triangles hq) hfg.symm hqg
                      have hqSG : q ∈ SG := Finset.mem_filter.mpr
                        ⟨hq, hqg, by omega, hqf'⟩
                      by_cases hqRoot : q = g
                      · subst q
                        have hpCard : (g.erase u).card = 2 := by
                          rw [Finset.card_erase_of_mem hug,
                            G.card_eq_three_of_mem_triangles hg]
                        have hpEdge := G.mem_edges_of_subset_triangle hg
                          (Finset.erase_subset _ _) hpCard
                        exact ⟨g.erase u, Finset.mem_inter.mpr
                          ⟨by simp [R], hpEdge⟩, Finset.erase_subset _ _⟩
                      · have hvq : v ∈ q := by
                          have : v ∈ q \ g := by rw [htipG hqSG hqRoot]; simp
                          exact (Finset.mem_sdiff.mp this).1
                        have hEraseCard : (g.erase u).card = 2 := by
                          rw [Finset.card_erase_of_mem hug,
                            G.card_eq_three_of_mem_triangles hg]
                        rcases subset_or_mem_of_large_trace hEraseCard
                            (sdiff_erase_eq_singleton hug) hqg with hsub | huq
                        · have hpEdge := G.mem_edges_of_subset_triangle hq hsub hEraseCard
                          exact ⟨g.erase u, Finset.mem_inter.mpr
                            ⟨by simp [R], hpEdge⟩, hsub⟩
                        · have hpSub : {u, v} ⊆ q := by
                            intro z hz
                            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                            exact hz.elim (fun h ↦ h ▸ huq) (fun h ↦ h ▸ hvq)
                          have hpCard : ({u, v} : Finset V).card = 2 := by simp [huv]
                          have hpEdge := G.mem_edges_of_subset_triangle hq hpSub hpCard
                          exact ⟨{u, v}, Finset.mem_inter.mpr
                            ⟨by simp [R], hpEdge⟩, hpSub⟩
              · change (R ∩ G.edges).card ≤ 6
                exact (Finset.card_le_card Finset.inter_subset_left).trans hRcard
        · have hvUnion : v ∉ e ∪ f := by
            intro hvUnion
            apply hvLoc
            exact Finset.mem_sdiff.mpr ⟨hvUnion, by simp [hvy]⟩
          have hg₁e : Disjoint g₁ e := by
            rw [hg₁Form, Finset.disjoint_left]
            intro z hz hze
            simp only [Finset.mem_insert] at hz
            rcases hz with rfl | hzB
            · exact hvUnion (Finset.mem_union_left _ hze)
            · exact (Finset.disjoint_left.mp hBdisjE) hzB hze
          have hg₁f : Disjoint g₁ f := by
            rw [hg₁Form, Finset.disjoint_left]
            intro z hz hzf
            simp only [Finset.mem_insert] at hz
            rcases hz with rfl | hzB
            · exact hvUnion (Finset.mem_union_right _ hzf)
            · exact (Finset.disjoint_left.mp hBdisjF) hzB hzf
          exact G.exists_six_transversal_of_isolated_packing_member
            hν hg₁ he hf hg₁e hg₁f (by omega)
      · have huUnion : u ∉ e ∪ g := by
          intro huUnion
          apply huLoc
          exact Finset.mem_sdiff.mpr ⟨huUnion, by simp [hux]⟩
        have hf₁e : Disjoint f₁ e := by
          rw [hf₁Form, Finset.disjoint_left]
          intro z hz hze
          simp only [Finset.mem_insert] at hz
          rcases hz with rfl | hzA
          · exact huUnion (Finset.mem_union_left _ hze)
          · exact (Finset.disjoint_left.mp hAdisjE) hzA hze
        have hf₁g : Disjoint f₁ g := by
          rw [hf₁Form, Finset.disjoint_left]
          intro z hz hzg
          simp only [Finset.mem_insert] at hz
          rcases hz with rfl | hzA
          · exact huUnion (Finset.mem_union_right _ hzg)
          · exact (Finset.disjoint_left.mp hAdisjG) hzA hzg
        exact G.exists_six_transversal_of_isolated_packing_member
          hν hf₁ he hg hf₁e hf₁g (by omega)
    · exact G.exists_six_transversal_of_no_opposite_pair_extension
        hν hg hyg (by
          intro q hq hBq
          by_contra hqg
          exact hExtG ⟨q, hq, hBq, hqg⟩)
  · exact G.exists_six_transversal_of_no_opposite_pair_extension
      hν hf hxf (by
        intro q hq hAq
        by_contra hqf
        exact hExtF ⟨q, hq, hAq, hqf⟩)

/-- Two vertex-disjoint graph triangles either supply the six-edge cover
directly or extend to an isolated/type-1a maximum three-packing. -/
theorem exists_six_transversal_of_disjoint_triangle_pair
    (hν : G.trianglePackingNumber ≤ 3)
    {a b : Finset V} (ha : a ∈ G.triangles) (hb : b ∈ G.triangles)
    (hab : Disjoint a b) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  let C₀ := a.powersetCard 2 ∪ b.powersetCard 2
  by_cases hcover : ∀ ⦃q⦄, q ∈ G.triangles →
      ∃ p ∈ C₀, p ⊆ q
  · refine ⟨C₀, ?_, ?_⟩
    · constructor
      · intro p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · have hpData := Finset.mem_powersetCard.mp hp
          exact G.mem_edges_of_subset_triangle ha hpData.1 hpData.2
        · have hpData := Finset.mem_powersetCard.mp hp
          exact G.mem_edges_of_subset_triangle hb hpData.1 hpData.2
      · exact hcover
    · have haCard := G.card_powersetCard_two_of_triangle ha
      have hbCard := G.card_powersetCard_two_of_triangle hb
      exact (Finset.card_union_le _ _).trans (by omega)
  · have hmiss : ∃ q ∈ G.triangles, ∀ p ∈ C₀, ¬p ⊆ q := by
      by_contra h
      apply hcover
      intro q hq
      by_contra hqCover
      exact h ⟨q, hq, by
        intro p hp hpq
        exact hqCover ⟨p, hp, hpq⟩⟩
    obtain ⟨q, hq, hqMiss⟩ := hmiss
    have hqa : (q ∩ a).card ≤ 1 := by
      by_contra h
      obtain ⟨p, hp, hpCard⟩ :=
        Finset.exists_subset_card_eq (s := q ∩ a) (n := 2) (by omega)
      have hpA : p ∈ a.powersetCard 2 :=
        Finset.mem_powersetCard.mpr
          ⟨hp.trans Finset.inter_subset_right, hpCard⟩
      exact hqMiss p (Finset.mem_union_left _ hpA)
        (hp.trans Finset.inter_subset_left)
    have hqb : (q ∩ b).card ≤ 1 := by
      by_contra h
      obtain ⟨p, hp, hpCard⟩ :=
        Finset.exists_subset_card_eq (s := q ∩ b) (n := 2) (by omega)
      have hpB : p ∈ b.powersetCard 2 :=
        Finset.mem_powersetCard.mpr
          ⟨hp.trans Finset.inter_subset_right, hpCard⟩
      exact hqMiss p (Finset.mem_union_right _ hpB)
        (hp.trans Finset.inter_subset_left)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqa with hqa0 | hqa1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqb with hqb0 | hqb1
      · have hqaDisj : Disjoint q a :=
          Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hqa0)
        have hqbDisj : Disjoint q b :=
          Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hqb0)
        exact G.exists_six_transversal_of_isolated_packing_member
          hν hq ha hb hqaDisj hqbDisj (by
            have hzero : (a ∩ b).card = 0 := by
              rw [Finset.card_eq_zero]
              exact Finset.disjoint_iff_inter_eq_empty.mp hab
            omega)
      · have haqDisj : Disjoint a q := by
          exact (Finset.disjoint_iff_inter_eq_empty.mpr
            (Finset.card_eq_zero.mp hqa0)).symm
        exact G.exists_six_transversal_of_isolated_packing_member
          hν ha hq hb haqDisj hab (by
            simpa [Finset.inter_comm] using hqb1.le)
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqb with hqb0 | hqb1
      · have hqbDisj : Disjoint q b :=
          Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hqb0)
        exact G.exists_six_transversal_of_isolated_packing_member
          hν hb hq ha hqbDisj.symm hab.symm hqa1.le
      · obtain ⟨x, hqaSet⟩ := Finset.card_eq_one.mp hqa1
        obtain ⟨y, hqbSet⟩ := Finset.card_eq_one.mp hqb1
        exact G.exists_six_transversal_of_type_one_a hν hq ha hb
          (by simpa [Finset.inter_comm] using hqaSet)
          (by simpa [Finset.inter_comm] using hqbSet) hab

/-- Parker's type-1b case: three packing triangles have one common vertex. -/
theorem exists_six_transversal_of_type_one_b
    (hν : G.trianglePackingNumber ≤ 3)
    {e f g : Finset V} {x : V}
    (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hg : g ∈ G.triangles)
    (hef : e ∩ f = {x}) (heg : e ∩ g = {x})
    (hfg : f ∩ g = {x}) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  have hxe : x ∈ e := by
    have : x ∈ e ∩ f := by simp [hef]
    exact (Finset.mem_inter.mp this).1
  have hxf : x ∈ f := by
    have : x ∈ e ∩ f := by simp [hef]
    exact (Finset.mem_inter.mp this).2
  have hxg : x ∈ g := by
    have : x ∈ e ∩ g := by simp [heg]
    exact (Finset.mem_inter.mp this).2
  let B := g.erase x
  have hBcard : B.card = 2 := by
    change (g.erase x).card = 2
    rw [Finset.card_erase_of_mem hxg,
      G.card_eq_three_of_mem_triangles hg]
  have hBg : B ⊆ g := Finset.erase_subset _ _
  have hBdisjE : Disjoint B e := by
    rw [Finset.disjoint_left]
    intro z hzB hze
    have hz : z ∈ e ∩ g := Finset.mem_inter.mpr ⟨hze, hBg hzB⟩
    have hzx : z = x := by simpa [heg] using hz
    exact (Finset.mem_erase.mp hzB).1 hzx
  have hBdisjF : Disjoint B f := by
    rw [Finset.disjoint_left]
    intro z hzB hzf
    have hz : z ∈ f ∩ g := Finset.mem_inter.mpr ⟨hzf, hBg hzB⟩
    have hzx : z = x := by simpa [hfg] using hz
    exact (Finset.mem_erase.mp hzB).1 hzx
  by_cases hExt : ∃ q ∈ G.triangles, B ⊆ q ∧ q ≠ g
  · obtain ⟨q, hq, hBq, hqg⟩ := hExt
    obtain ⟨u, huB, hqForm⟩ :=
      exists_eq_insert_of_subset_card_two_card_three hBcard
        (G.card_eq_three_of_mem_triangles hq) hBq
    have hux : u ≠ x := by
      intro hux
      subst u
      apply hqg
      rw [hqForm]
      simpa [B] using Finset.insert_erase hxg
    by_cases hue : u ∈ e
    · have huf : u ∉ f := by
        intro huf
        have hmem : u ∈ e ∩ f := Finset.mem_inter.mpr ⟨hue, huf⟩
        have : u = x := by simpa [hef] using hmem
        exact hux this
      have hqf : Disjoint q f := by
        rw [hqForm, Finset.disjoint_left]
        intro z hz hzf
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hzB
        · exact huf hzf
        · exact (Finset.disjoint_left.mp hBdisjF) hzB hzf
      exact G.exists_six_transversal_of_disjoint_triangle_pair hν hq hf hqf
    · have hqe : Disjoint q e := by
        rw [hqForm, Finset.disjoint_left]
        intro z hz hze
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hzB
        · exact hue hze
        · exact (Finset.disjoint_left.mp hBdisjE) hzB hze
      exact G.exists_six_transversal_of_disjoint_triangle_pair hν hq he hqe
  · exact G.exists_six_transversal_of_no_opposite_pair_extension
      hν hg hxg (by
        intro q hq hBq
        by_contra hqg
        exact hExt ⟨q, hq, hBq, hqg⟩)

/-- Parker's type-1c case: the three pairwise intersections of the packing
members are distinct. -/
theorem exists_six_transversal_of_type_one_c
    (hν : G.trianglePackingNumber ≤ 3)
    {e f g : Finset V} {x y z : V}
    (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hg : g ∈ G.triangles)
    (hef : e ∩ f = {x}) (hfg : f ∩ g = {y})
    (heg : e ∩ g = {z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  by_cases hdisj : ∃ a ∈ G.triangles, ∃ b ∈ G.triangles, Disjoint a b
  · obtain ⟨a, ha, b, hb, hab⟩ := hdisj
    exact G.exists_six_transversal_of_disjoint_triangle_pair hν ha hb hab
  · have hNoDisj : ∀ ⦃a⦄, a ∈ G.triangles →
        ∀ ⦃b⦄, b ∈ G.triangles → ¬Disjoint a b := by
      intro a ha b hb hab
      exact hdisj ⟨a, ha, b, hb, hab⟩
    have hxe : x ∈ e := by
      have : x ∈ e ∩ f := by simp [hef]
      exact (Finset.mem_inter.mp this).1
    have hxf : x ∈ f := by
      have : x ∈ e ∩ f := by simp [hef]
      exact (Finset.mem_inter.mp this).2
    have hyf : y ∈ f := by
      have : y ∈ f ∩ g := by simp [hfg]
      exact (Finset.mem_inter.mp this).1
    have hyg : y ∈ g := by
      have : y ∈ f ∩ g := by simp [hfg]
      exact (Finset.mem_inter.mp this).2
    have hze : z ∈ e := by
      have : z ∈ e ∩ g := by simp [heg]
      exact (Finset.mem_inter.mp this).1
    have hzg : z ∈ g := by
      have : z ∈ e ∩ g := by simp [heg]
      exact (Finset.mem_inter.mp this).2
    have hExzCard : ({x, z} : Finset V).card = 2 := by simp [hxz]
    have hFxyCard : ({x, y} : Finset V).card = 2 := by simp [hxy]
    have hGyzCard : ({y, z} : Finset V).card = 2 := by simp [hyz]
    have hExz : ({x, z} : Finset V) ⊆ e := pair_subset_of_mem hxe hze
    have hFxy : ({x, y} : Finset V) ⊆ f := pair_subset_of_mem hxf hyf
    have hGyz : ({y, z} : Finset V) ⊆ g := pair_subset_of_mem hyg hzg
    obtain ⟨b, hbPair, heForm⟩ :=
      exists_eq_insert_of_subset_card_two_card_three hExzCard
        (G.card_eq_three_of_mem_triangles he) hExz
    obtain ⟨a, haPair, hfForm⟩ :=
      exists_eq_insert_of_subset_card_two_card_three hFxyCard
        (G.card_eq_three_of_mem_triangles hf) hFxy
    obtain ⟨c, hcPair, hgForm⟩ :=
      exists_eq_insert_of_subset_card_two_card_three hGyzCard
        (G.card_eq_three_of_mem_triangles hg) hGyz
    have hxc : x ≠ c := by
      intro hxc
      subst c
      have hxg : x ∈ g := by simp [hgForm]
      have hxeg : x ∈ e ∩ g := Finset.mem_inter.mpr ⟨hxe, hxg⟩
      have hxz' : x = z := by simpa [heg] using hxeg
      exact hxz hxz'
    have hyb : y ≠ b := by
      intro hyb
      subst b
      have hye : y ∈ e := by simp [heForm]
      have hyef : y ∈ e ∩ f := Finset.mem_inter.mpr ⟨hye, hyf⟩
      have hyx : y = x := by simpa [hef] using hyef
      exact hxy hyx.symm
    have hza : z ≠ a := by
      intro hza
      subst a
      have hzf : z ∈ f := by simp [hfForm]
      have hzfg : z ∈ f ∩ g := Finset.mem_inter.mpr ⟨hzf, hzg⟩
      have hzy : z = y := by simpa [hfg] using hzfg
      exact hyz hzy.symm
    let R : Finset (Finset V) :=
      {{x, y}, {x, z}, {y, z}, {x, c}, {y, b}, {z, a}}
    let C : Finset (Finset V) := R ∩ G.edges
    have hRcard : R.card ≤ 6 := by
      change ({{x, y}, {x, z}, {y, z}, {x, c}, {y, b}, {z, a}} :
        Finset (Finset V)).card ≤ 6
      exact Finset.card_le_six
    have hRtwo : ∀ ⦃p⦄, p ∈ R → p.card = 2 := by
      intro p hp
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp | hp | hp | hp | hp
      · rw [hp]; simp [hxy]
      · rw [hp]; simp [hxz]
      · rw [hp]; simp [hyz]
      · rw [hp]; simp [hxc]
      · rw [hp]; simp [hyb]
      · rw [hp]; simp [hza]
    refine ⟨C, ?_, ?_⟩
    · constructor
      · exact Finset.inter_subset_right
      · intro q hq
        have hnear := G.near_one_of_packing_triple hν he hf hg hq
          (by simp [hef]) (by simp [heg]) (by simp [hfg])
        have hraw : ∃ p ∈ R, p ⊆ q := by
          rcases hnear with hqe | hqf | hqg
          · by_cases hxq : x ∈ q <;> by_cases hzq : z ∈ q <;>
              by_cases hbq : b ∈ q
            · exact ⟨{x, z}, by simp [R], pair_subset_of_mem hxq hzq⟩
            · exact ⟨{x, z}, by simp [R], pair_subset_of_mem hxq hzq⟩
            · obtain ⟨w, hwq, hwg⟩ := Finset.not_disjoint_iff.mp
                (hNoDisj hq hg)
              simp only [hgForm, Finset.mem_insert,
                Finset.mem_singleton] at hwg
              rcases hwg with hwc | hwy | hwz
              · have hcq : c ∈ q := by simpa [hwc] using hwq
                exact ⟨{x, c}, by simp [R], pair_subset_of_mem hxq hcq⟩
              · have hyq : y ∈ q := by simpa [hwy] using hwq
                exact ⟨{y, b}, by simp [R], pair_subset_of_mem hyq hbq⟩
              · have hzq : z ∈ q := by simpa [hwz] using hwq
                exact ⟨{x, z}, by simp [R], pair_subset_of_mem hxq hzq⟩
            · simp [heForm, hxq, hzq, hbq] at hqe
            · obtain ⟨w, hwq, hwf⟩ := Finset.not_disjoint_iff.mp
                (hNoDisj hq hf)
              simp only [hfForm, Finset.mem_insert,
                Finset.mem_singleton] at hwf
              rcases hwf with hwa | hwx | hwy
              · have haq : a ∈ q := by simpa [hwa] using hwq
                exact ⟨{z, a}, by simp [R], pair_subset_of_mem hzq haq⟩
              · have hxq' : x ∈ q := by simpa [hwx] using hwq
                exact (hxq hxq').elim
              · have hyq : y ∈ q := by simpa [hwy] using hwq
                exact ⟨{y, b}, by simp [R], pair_subset_of_mem hyq hbq⟩
            · simp [heForm, hxq, hzq, hbq] at hqe
            · simp [heForm, hxq, hzq, hbq] at hqe
            · simp [heForm, hxq, hzq, hbq] at hqe
          · by_cases hxq : x ∈ q <;> by_cases hyq : y ∈ q <;>
              by_cases haq : a ∈ q
            · exact ⟨{x, y}, by simp [R], pair_subset_of_mem hxq hyq⟩
            · exact ⟨{x, y}, by simp [R], pair_subset_of_mem hxq hyq⟩
            · obtain ⟨w, hwq, hwg⟩ := Finset.not_disjoint_iff.mp
                (hNoDisj hq hg)
              simp only [hgForm, Finset.mem_insert,
                Finset.mem_singleton] at hwg
              rcases hwg with hwc | hwy | hwz
              · have hcq : c ∈ q := by simpa [hwc] using hwq
                exact ⟨{x, c}, by simp [R], pair_subset_of_mem hxq hcq⟩
              · have hyq' : y ∈ q := by simpa [hwy] using hwq
                exact ⟨{x, y}, by simp [R], pair_subset_of_mem hxq hyq'⟩
              · have hzq : z ∈ q := by simpa [hwz] using hwq
                exact ⟨{z, a}, by simp [R], pair_subset_of_mem hzq haq⟩
            · simp [hfForm, hxq, hyq, haq] at hqf
            · obtain ⟨w, hwq, hwe⟩ := Finset.not_disjoint_iff.mp
                (hNoDisj hq he)
              simp only [heForm, Finset.mem_insert,
                Finset.mem_singleton] at hwe
              rcases hwe with hwb | hwx | hwz
              · have hbq : b ∈ q := by simpa [hwb] using hwq
                exact ⟨{y, b}, by simp [R], pair_subset_of_mem hyq hbq⟩
              · have hxq' : x ∈ q := by simpa [hwx] using hwq
                exact ⟨{x, y}, by simp [R], pair_subset_of_mem hxq' hyq⟩
              · have hzq : z ∈ q := by simpa [hwz] using hwq
                exact ⟨{z, a}, by simp [R], pair_subset_of_mem hzq haq⟩
            · simp [hfForm, hxq, hyq, haq] at hqf
            · simp [hfForm, hxq, hyq, haq] at hqf
            · simp [hfForm, hxq, hyq, haq] at hqf
          · by_cases hyq : y ∈ q <;> by_cases hzq : z ∈ q <;>
              by_cases hcq : c ∈ q
            · exact ⟨{y, z}, by simp [R], pair_subset_of_mem hyq hzq⟩
            · exact ⟨{y, z}, by simp [R], pair_subset_of_mem hyq hzq⟩
            · obtain ⟨w, hwq, hwe⟩ := Finset.not_disjoint_iff.mp
                (hNoDisj hq he)
              simp only [heForm, Finset.mem_insert,
                Finset.mem_singleton] at hwe
              rcases hwe with hwb | hwx | hwz
              · have hbq : b ∈ q := by simpa [hwb] using hwq
                exact ⟨{y, b}, by simp [R], pair_subset_of_mem hyq hbq⟩
              · have hxq : x ∈ q := by simpa [hwx] using hwq
                exact ⟨{x, c}, by simp [R], pair_subset_of_mem hxq hcq⟩
              · have hzq' : z ∈ q := by simpa [hwz] using hwq
                exact ⟨{y, z}, by simp [R], pair_subset_of_mem hyq hzq'⟩
            · simp [hgForm, hyq, hzq, hcq] at hqg
            · obtain ⟨w, hwq, hwf⟩ := Finset.not_disjoint_iff.mp
                (hNoDisj hq hf)
              simp only [hfForm, Finset.mem_insert,
                Finset.mem_singleton] at hwf
              rcases hwf with hwa | hwx | hwy
              · have haq : a ∈ q := by simpa [hwa] using hwq
                exact ⟨{z, a}, by simp [R], pair_subset_of_mem hzq haq⟩
              · have hxq : x ∈ q := by simpa [hwx] using hwq
                exact ⟨{x, c}, by simp [R], pair_subset_of_mem hxq hcq⟩
              · have hyq : y ∈ q := by simpa [hwy] using hwq
                exact ⟨{y, z}, by simp [R], pair_subset_of_mem hyq hzq⟩
            · simp [hgForm, hyq, hzq, hcq] at hqg
            · simp [hgForm, hyq, hzq, hcq] at hqg
            · simp [hgForm, hyq, hzq, hcq] at hqg
        obtain ⟨p, hpR, hpq⟩ := hraw
        have hpCard := hRtwo hpR
        have hpEdge := G.mem_edges_of_subset_triangle hq hpq hpCard
        exact ⟨p, Finset.mem_inter.mpr ⟨hpR, hpEdge⟩, hpq⟩
    · change (R ∩ G.edges).card ≤ 6
      exact (Finset.card_le_card Finset.inter_subset_left).trans hRcard

/-- Every packing triple has a six-edge transversal.  The proof first removes
the cases containing a vertex-disjoint pair, then distinguishes whether the
three singleton pairwise intersections agree. -/
theorem exists_six_transversal_of_packing_triple
    (hν : G.trianglePackingNumber ≤ 3)
    {e f g : Finset V}
    (he : e ∈ G.triangles) (hf : f ∈ G.triangles)
    (hg : g ∈ G.triangles)
    (hef : (e ∩ f).card ≤ 1) (heg : (e ∩ g).card ≤ 1)
    (hfg : (f ∩ g).card ≤ 1) :
    ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ 6 := by
  classical
  by_cases hefDisj : Disjoint e f
  · exact G.exists_six_transversal_of_disjoint_triangle_pair hν he hf hefDisj
  by_cases hegDisj : Disjoint e g
  · exact G.exists_six_transversal_of_disjoint_triangle_pair hν he hg hegDisj
  by_cases hfgDisj : Disjoint f g
  · exact G.exists_six_transversal_of_disjoint_triangle_pair hν hf hg hfgDisj
  have hefNeZero : (e ∩ f).card ≠ 0 := by
    intro hzero
    apply hefDisj
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  have hegNeZero : (e ∩ g).card ≠ 0 := by
    intro hzero
    apply hegDisj
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  have hfgNeZero : (f ∩ g).card ≠ 0 := by
    intro hzero
    apply hfgDisj
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  have hefOne : (e ∩ f).card = 1 := by omega
  have hegOne : (e ∩ g).card = 1 := by omega
  have hfgOne : (f ∩ g).card = 1 := by omega
  obtain ⟨x, hefSet⟩ := Finset.card_eq_one.mp hefOne
  obtain ⟨z, hegSet⟩ := Finset.card_eq_one.mp hegOne
  obtain ⟨y, hfgSet⟩ := Finset.card_eq_one.mp hfgOne
  by_cases hxy : x = y
  · have hxe : x ∈ e := by
      have : x ∈ e ∩ f := by simp [hefSet]
      exact (Finset.mem_inter.mp this).1
    have hxg : x ∈ g := by
      have : y ∈ f ∩ g := by simp [hfgSet]
      exact hxy ▸ (Finset.mem_inter.mp this).2
    have hxz : x = z := by
      have : x ∈ e ∩ g := Finset.mem_inter.mpr ⟨hxe, hxg⟩
      simpa [hegSet] using this
    apply G.exists_six_transversal_of_type_one_b hν he hf hg hefSet
    · simpa [← hxz] using hegSet
    · simpa [← hxy] using hfgSet
  by_cases hxz : x = z
  · have hxf : x ∈ f := by
      have : x ∈ e ∩ f := by simp [hefSet]
      exact (Finset.mem_inter.mp this).2
    have hxg : x ∈ g := by
      have : z ∈ e ∩ g := by simp [hegSet]
      exact hxz ▸ (Finset.mem_inter.mp this).2
    have hxy' : x = y := by
      have : x ∈ f ∩ g := Finset.mem_inter.mpr ⟨hxf, hxg⟩
      simpa [hfgSet] using this
    apply G.exists_six_transversal_of_type_one_b hν he hf hg hefSet
    · simpa [← hxz] using hegSet
    · simpa [← hxy'] using hfgSet
  by_cases hyz : y = z
  · have hyf : y ∈ f := by
      have : y ∈ f ∩ g := by simp [hfgSet]
      exact (Finset.mem_inter.mp this).1
    have hye : y ∈ e := by
      have : z ∈ e ∩ g := by simp [hegSet]
      exact hyz ▸ (Finset.mem_inter.mp this).1
    have hyx : y = x := by
      have : y ∈ e ∩ f := Finset.mem_inter.mpr ⟨hye, hyf⟩
      simpa [hefSet] using this
    apply G.exists_six_transversal_of_type_one_b hν he hf hg
    · simpa [← hyx] using hefSet
    · simpa [← hyz] using hegSet
    · exact hfgSet
  exact G.exists_six_transversal_of_type_one_c hν he hf hg
    hefSet hfgSet hegSet hxy hxz hyz

/-- Parker's theorem at packing rank three, stated in the graph language used
by the main rank-four theorem. -/
theorem tuza_of_trianglePackingNumber_le_three
    (hν : G.trianglePackingNumber ≤ 3) :
    G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber := by
  classical
  by_cases hνtwo : G.trianglePackingNumber ≤ 2
  · exact G.tuza_of_trianglePackingNumber_le_two hνtwo
  have hνeq : G.trianglePackingNumber = 3 := by omega
  obtain ⟨P, hP, hPcard⟩ := G.exists_max_trianglePacking
  have hPcardThree : P.card = 3 := hPcard.trans hνeq
  obtain ⟨e, f, g, hefNe, hegNe, hfgNe, rfl⟩ :=
    Finset.card_eq_three.mp hPcardThree
  have he : e ∈ G.triangles := hP.1 (by simp)
  have hf : f ∈ G.triangles := hP.1 (by simp)
  have hg : g ∈ G.triangles := hP.1 (by simp)
  have hef : (e ∩ f).card ≤ 1 := hP.2 (by simp) (by simp) hefNe
  have heg : (e ∩ g).card ≤ 1 := hP.2 (by simp) (by simp) hegNe
  have hfg : (f ∩ g).card ≤ 1 := hP.2 (by simp) (by simp) hfgNe
  obtain ⟨C, hC, hCcard⟩ :=
    G.exists_six_transversal_of_packing_triple hν he hf hg hef heg hfg
  calc
    G.triangleTransversalNumber ≤ C.card :=
      G.triangleTransversalNumber_le_card hC
    _ ≤ 6 := hCcard
    _ = 2 * G.trianglePackingNumber := by omega

end SimpleGraph
