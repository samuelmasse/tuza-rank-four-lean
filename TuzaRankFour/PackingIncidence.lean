import TuzaRankFour.PackingClassificationResult

/-!
# Incidence representation of an ordered four-packing

Vertices are grouped by the subset of the four packed triangles that contain
them.  The non-singleton incidence masks are exactly the finite objects
classified in `PackingClassificationResult`.
-/

namespace TuzaRankFour.PackingClassification

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Incidence mask of a vertex with respect to four ordered blocks. -/
def incidence (T : Block → Finset V) (v : V) : Mask :=
  Finset.univ.filter fun i => v ∈ T i

@[simp]
theorem mem_incidence_iff (T : Block → Finset V) (v : V) (i : Block) :
    i ∈ incidence T v ↔ v ∈ T i := by
  simp [incidence]

/-- Vertices with a prescribed incidence mask. -/
def incidenceFiber (T : Block → Finset V) (m : Mask) : Finset V :=
  Finset.univ.filter fun v => incidence T v = m

/-- Non-singleton incidence masks realized by the four blocks. -/
def sharedFamilyOf (T : Block → Finset V) : SharedFamily :=
  ((Finset.univ : Finset V).image (incidence T)).filter fun m => 2 ≤ m.card

theorem mem_sharedFamilyOf_iff (T : Block → Finset V) (m : Mask) :
    m ∈ sharedFamilyOf T ↔
      2 ≤ m.card ∧ (incidenceFiber T m).Nonempty := by
  simp only [sharedFamilyOf, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨v, hv⟩, hcard⟩
    refine ⟨hcard, ⟨v, ?_⟩⟩
    simp [incidenceFiber, hv]
  · rintro ⟨hcard, ⟨v, hv⟩⟩
    refine ⟨⟨v, ?_⟩, hcard⟩
    exact (Finset.mem_filter.mp hv).2

/-- The hypotheses supplied by four pairwise edge-disjoint triangles. -/
def IsLinearTripleFamily (T : Block → Finset V) : Prop :=
  (∀ i, (T i).card = 3) ∧
  (∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)

instance instDecidableIsLinearTripleFamily (T : Block → Finset V) :
    Decidable (IsLinearTripleFamily T) := by
  unfold IsLinearTripleFamily
  infer_instance

theorem incidenceFiber_card_le_one (T : Block → Finset V)
    (hLinear : IsLinearTripleFamily T) (m : Mask) (hm : 2 ≤ m.card) :
    (incidenceFiber T m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < m.card)
  have hui : u ∈ T i := by
    have := (Finset.mem_filter.mp hu).2
    rw [← this] at hi
    exact (mem_incidence_iff T u i).mp hi
  have huvj : u ∈ T j := by
    have := (Finset.mem_filter.mp hu).2
    rw [← this] at hj
    exact (mem_incidence_iff T u j).mp hj
  have hvi : v ∈ T i := by
    have := (Finset.mem_filter.mp hv).2
    rw [← this] at hi
    exact (mem_incidence_iff T v i).mp hi
  have hvj : v ∈ T j := by
    have := (Finset.mem_filter.mp hv).2
    rw [← this] at hj
    exact (mem_incidence_iff T v j).mp hj
  exact Finset.card_le_one.mp (hLinear.2 i j hij) u
    (Finset.mem_inter.mpr ⟨hui, huvj⟩) v
    (Finset.mem_inter.mpr ⟨hvi, hvj⟩)

theorem sharedFamilyOf_valid (T : Block → Finset V)
    (hLinear : IsLinearTripleFamily T) :
    validBool (sharedFamilyOf T) = true := by
  rw [validBool_eq_true_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    exact (mem_sharedFamilyOf_iff T m).mp hm |>.1
  · intro i
    let target := (T i).image (incidence T)
    have hsub : (sharedFamilyOf T).filter (fun m => i ∈ m) ⊆ target := by
      intro m hm
      obtain ⟨hmFamily, him⟩ := Finset.mem_filter.mp hm
      obtain ⟨hcard, ⟨v, hvFiber⟩⟩ :=
        (mem_sharedFamilyOf_iff T m).mp hmFamily
      have hvMask := (Finset.mem_filter.mp hvFiber).2
      apply Finset.mem_image.mpr
      refine ⟨v, ?_, hvMask⟩
      rw [← mem_incidence_iff T v i, hvMask]
      exact him
    calc
      ((sharedFamilyOf T).filter fun m => i ∈ m).card ≤ target.card :=
        Finset.card_le_card hsub
      _ ≤ (T i).card := Finset.card_image_le
      _ = 3 := hLinear.1 i
  · intro i j
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      let target := (T i ∩ T j).image (incidence T)
      have hsub :
          (sharedFamilyOf T).filter (fun m => i ∈ m ∧ j ∈ m) ⊆ target := by
        intro m hm
        obtain ⟨hmFamily, him, hjm⟩ := Finset.mem_filter.mp hm
        obtain ⟨hcard, ⟨v, hvFiber⟩⟩ :=
          (mem_sharedFamilyOf_iff T m).mp hmFamily
        have hvMask := (Finset.mem_filter.mp hvFiber).2
        apply Finset.mem_image.mpr
        refine ⟨v, Finset.mem_inter.mpr ⟨?_, ?_⟩, hvMask⟩
        · rw [← mem_incidence_iff T v i, hvMask]
          exact him
        · rw [← mem_incidence_iff T v j, hvMask]
          exact hjm
      calc
        ((sharedFamilyOf T).filter fun m => i ∈ m ∧ j ∈ m).card ≤
            target.card := Finset.card_le_card hsub
        _ ≤ (T i ∩ T j).card := Finset.card_image_le
        _ ≤ 1 := hLinear.2 i j hij

/-- Reorder the four blocks by a permutation. -/
def reindex (p : Equiv.Perm Block) (T : Block → Finset V) :
    Block → Finset V :=
  fun i => T (p.symm i)

theorem incidence_reindex (p : Equiv.Perm Block) (T : Block → Finset V)
    (v : V) :
    incidence (reindex p T) v =
      (incidence T v).map p.toEmbedding := by
  ext i
  simp [incidence, reindex]

theorem isLinearTripleFamily_reindex (p : Equiv.Perm Block)
    (T : Block → Finset V) (hT : IsLinearTripleFamily T) :
    IsLinearTripleFamily (reindex p T) := by
  constructor
  · intro i
    exact hT.1 (p.symm i)
  · intro i j hij
    apply hT.2 (p.symm i) (p.symm j)
    intro h
    exact hij (p.symm.injective h)

theorem sharedFamilyOf_reindex (p : Equiv.Perm Block)
    (T : Block → Finset V) :
    sharedFamilyOf (reindex p T) =
      permuteFamily p (sharedFamilyOf T) := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨hmImage, hcard⟩ := Finset.mem_filter.mp hm
    obtain ⟨v, hvUniv, hv⟩ := Finset.mem_image.mp hmImage
    rw [incidence_reindex] at hv
    apply Finset.mem_map.mpr
    refine ⟨incidence T v, ?_, hv⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨v, hvUniv, rfl⟩, ?_⟩
    simpa [← hv] using hcard
  · intro hm
    obtain ⟨a, ha, ham⟩ := Finset.mem_map.mp hm
    obtain ⟨haImage, haCard⟩ := Finset.mem_filter.mp ha
    obtain ⟨v, hvUniv, hva⟩ := Finset.mem_image.mp haImage
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨v, hvUniv, ?_⟩, ?_⟩
    · rw [incidence_reindex, hva]
      exact ham
    · rw [← ham]
      simpa using haCard

/-- The masks containing a fixed block index. -/
def masksContaining (i : Block) : Finset Mask :=
  Finset.univ.filter fun m => i ∈ m

theorem sum_incidenceFiber_containing (T : Block → Finset V) (i : Block) :
    ∑ m ∈ masksContaining i, (incidenceFiber T m).card = (T i).card := by
  simpa [masksContaining, incidenceFiber] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset V) (masksContaining i) (incidence T))

theorem sum_incidenceFiber_univ (T : Block → Finset V) :
    ∑ m : Mask, (incidenceFiber T m).card = Fintype.card V := by
  simpa [incidenceFiber] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset V) (Finset.univ : Finset Mask) (incidence T))

theorem incidenceFiber_card_eq_of_two_le
    (T U : Block → Finset V)
    (hT : IsLinearTripleFamily T) (hU : IsLinearTripleFamily U)
    (hFamily : sharedFamilyOf T = sharedFamilyOf U)
    (m : Mask) (hm : 2 ≤ m.card) :
    (incidenceFiber T m).card = (incidenceFiber U m).card := by
  have hmem : m ∈ sharedFamilyOf T ↔ m ∈ sharedFamilyOf U := by
    rw [hFamily]
  by_cases hmT : m ∈ sharedFamilyOf T
  · have hmU := hmem.mp hmT
    have hTpos : 0 < (incidenceFiber T m).card :=
      Finset.card_pos.mpr ((mem_sharedFamilyOf_iff T m).mp hmT).2
    have hUpos : 0 < (incidenceFiber U m).card :=
      Finset.card_pos.mpr ((mem_sharedFamilyOf_iff U m).mp hmU).2
    have hTle := incidenceFiber_card_le_one T hT m hm
    have hUle := incidenceFiber_card_le_one U hU m hm
    omega
  · have hmU : m ∉ sharedFamilyOf U := by
      intro h
      exact hmT (hmem.mpr h)
    have hTzero : (incidenceFiber T m).card = 0 := by
      by_contra h
      apply hmT
      apply (mem_sharedFamilyOf_iff T m).mpr
      exact ⟨hm, Finset.card_pos.mp (Nat.pos_of_ne_zero h)⟩
    have hUzero : (incidenceFiber U m).card = 0 := by
      by_contra h
      apply hmU
      apply (mem_sharedFamilyOf_iff U m).mpr
      exact ⟨hm, Finset.card_pos.mp (Nat.pos_of_ne_zero h)⟩
    omega

theorem incidenceFiber_card_eq_indicator
    (T : Block → Finset V) (hT : IsLinearTripleFamily T)
    (m : Mask) (hm : 2 ≤ m.card) :
    (incidenceFiber T m).card =
      if m ∈ sharedFamilyOf T then 1 else 0 := by
  by_cases hmem : m ∈ sharedFamilyOf T
  · simp only [if_pos hmem]
    have hpos : 0 < (incidenceFiber T m).card :=
      Finset.card_pos.mpr ((mem_sharedFamilyOf_iff T m).mp hmem).2
    have hle := incidenceFiber_card_le_one T hT m hm
    omega
  · simp only [if_neg hmem]
    by_contra h
    apply hmem
    apply (mem_sharedFamilyOf_iff T m).mpr
    exact ⟨hm, Finset.card_pos.mp (Nat.pos_of_ne_zero h)⟩

/-- Number of shared masks incident with a fixed block. -/
def sharedDegree (F : SharedFamily) (i : Block) : Nat :=
  (F.filter fun m => i ∈ m).card

theorem incidenceFiber_singleton_card
    (T : Block → Finset V) (hT : IsLinearTripleFamily T) (i : Block) :
    (incidenceFiber T {i}).card =
      3 - sharedDegree (sharedFamilyOf T) i := by
  let S := masksContaining i
  have hmem : ({i} : Mask) ∈ S := by simp [S, masksContaining]
  have hrestMasks :
      (S.erase {i}).filter (fun a => a ∈ sharedFamilyOf T) =
        (sharedFamilyOf T).filter (fun a => i ∈ a) := by
    ext a
    constructor
    · intro ha
      obtain ⟨haErase, haFamily⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr
        ⟨haFamily, (Finset.mem_filter.mp (Finset.mem_of_mem_erase haErase)).2⟩
    · intro ha
      obtain ⟨haFamily, hai⟩ := Finset.mem_filter.mp ha
      have haCard := (mem_sharedFamilyOf_iff T a).mp haFamily |>.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_erase.mpr ⟨?_, ?_⟩, haFamily⟩
      · intro h
        subst a
        simp at haCard
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
  have hrestSum :
      ∑ a ∈ S.erase {i}, (incidenceFiber T a).card =
        sharedDegree (sharedFamilyOf T) i := by
    calc
      (∑ a ∈ S.erase {i}, (incidenceFiber T a).card) =
          ∑ a ∈ S.erase {i}, if a ∈ sharedFamilyOf T then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            have hai : i ∈ a :=
              (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha)).2
            have hane : a ≠ ({i} : Mask) := (Finset.mem_erase.mp ha).1
            have hcard : 2 ≤ a.card := by
              have hpos : 0 < a.card := Finset.card_pos.mpr ⟨i, hai⟩
              by_contra h
              have hone : a.card = 1 := by omega
              obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
              subst a
              simp at hai
              subst j
              exact hane rfl
            exact incidenceFiber_card_eq_indicator T hT a hcard
      _ = ((S.erase {i}).filter fun a => a ∈ sharedFamilyOf T).card := by
            simpa only [Nat.cast_id] using
              (Finset.sum_boole (R := Nat)
                (fun a => a ∈ sharedFamilyOf T) (S.erase {i}))
      _ = sharedDegree (sharedFamilyOf T) i := by
            rw [hrestMasks]
            rfl
  have hsum := sum_incidenceFiber_containing T i
  have hsplit := S.sum_erase_add
    (fun a => (incidenceFiber T a).card) hmem
  change (∑ a ∈ S, (incidenceFiber T a).card) = (T i).card at hsum
  rw [hT.1 i] at hsum
  omega

/-- Singleton masks, one for each of the four blocks. -/
def singletonMasks : Finset Mask :=
  (Finset.univ : Finset Block).image fun i => {i}

/-- Number of vertices forced by a valid shared-incidence family: one for
each shared mask and the remaining private vertices in each block. -/
def requiredOrder (F : SharedFamily) : Nat :=
  F.card + ∑ i : Block, (3 - sharedDegree F i)

theorem sharedFamily_disjoint_singletonMasks (T : Block → Finset V) :
    Disjoint (sharedFamilyOf T) singletonMasks := by
  rw [Finset.disjoint_left]
  intro m hmFamily hmSingleton
  obtain ⟨i, hi, him⟩ := Finset.mem_image.mp hmSingleton
  subst m
  have hcard := (mem_sharedFamilyOf_iff T {i}).mp hmFamily |>.1
  simp at hcard

theorem requiredOrder_le_card
    (T : Block → Finset V) (hT : IsLinearTripleFamily T) :
    requiredOrder (sharedFamilyOf T) ≤ Fintype.card V := by
  let F := sharedFamilyOf T
  have hDisjoint : Disjoint F singletonMasks :=
    sharedFamily_disjoint_singletonMasks T
  have hSharedSum :
      ∑ m ∈ F, (incidenceFiber T m).card = F.card := by
    calc
      (∑ m ∈ F, (incidenceFiber T m).card) = ∑ _m ∈ F, 1 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmCard := (mem_sharedFamilyOf_iff T m).mp hm |>.1
        rw [incidenceFiber_card_eq_indicator T hT m hmCard, if_pos hm]
      _ = F.card := by simp
  have hSingletonSum :
      ∑ m ∈ singletonMasks, (incidenceFiber T m).card =
        ∑ i : Block, (incidenceFiber T {i}).card := by
    unfold singletonMasks
    rw [Finset.sum_image]
    intro i hi j hj hij
    simpa using hij
  have hSelectedLe :
      ∑ m ∈ F ∪ singletonMasks, (incidenceFiber T m).card ≤
        ∑ m : Mask, (incidenceFiber T m).card := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  calc
    requiredOrder F =
        (∑ m ∈ F, (incidenceFiber T m).card) +
          ∑ m ∈ singletonMasks, (incidenceFiber T m).card := by
      rw [hSharedSum, hSingletonSum]
      simp_rw [incidenceFiber_singleton_card T hT]
      simp [requiredOrder, F]
    _ = ∑ m ∈ F ∪ singletonMasks, (incidenceFiber T m).card := by
      rw [Finset.sum_union hDisjoint]
    _ ≤ ∑ m : Mask, (incidenceFiber T m).card := hSelectedLe
    _ = Fintype.card V := sum_incidenceFiber_univ T

theorem incidenceFiber_card_eq_of_card_one
    (T U : Block → Finset V)
    (hT : IsLinearTripleFamily T) (hU : IsLinearTripleFamily U)
    (hFamily : sharedFamilyOf T = sharedFamilyOf U)
    (m : Mask) (hm : m.card = 1) :
    (incidenceFiber T m).card = (incidenceFiber U m).card := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hm
  let S := masksContaining i
  have hmem : ({i} : Mask) ∈ S := by simp [S, masksContaining]
  have hrest :
      ∑ a ∈ S.erase {i}, (incidenceFiber T a).card =
        ∑ a ∈ S.erase {i}, (incidenceFiber U a).card := by
    apply Finset.sum_congr rfl
    intro a ha
    have hai : i ∈ a := by
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha)).2
    have hane : a ≠ ({i} : Mask) := (Finset.mem_erase.mp ha).1
    have hacard : 2 ≤ a.card := by
      have hpos : 0 < a.card := Finset.card_pos.mpr ⟨i, hai⟩
      by_contra h
      have hone : a.card = 1 := by omega
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
      subst a
      simp at hai
      subst j
      exact hane rfl
    exact incidenceFiber_card_eq_of_two_le T U hT hU hFamily a hacard
  have hsumT := sum_incidenceFiber_containing T i
  have hsumU := sum_incidenceFiber_containing U i
  have hsplitT := S.sum_erase_add
    (fun a => (incidenceFiber T a).card) hmem
  have hsplitU := S.sum_erase_add
    (fun a => (incidenceFiber U a).card) hmem
  change (∑ a ∈ S, (incidenceFiber T a).card) = (T i).card at hsumT
  change (∑ a ∈ S, (incidenceFiber U a).card) = (U i).card at hsumU
  rw [hT.1 i] at hsumT
  rw [hU.1 i] at hsumU
  omega

theorem incidenceFiber_card_eq_of_card_zero
    (T U : Block → Finset V)
    (hT : IsLinearTripleFamily T) (hU : IsLinearTripleFamily U)
    (hFamily : sharedFamilyOf T = sharedFamilyOf U)
    (m : Mask) (hm : m.card = 0) :
    (incidenceFiber T m).card = (incidenceFiber U m).card := by
  have hmEmpty : m = ∅ := Finset.card_eq_zero.mp hm
  subst m
  let S : Finset Mask := Finset.univ
  have hmem : (∅ : Mask) ∈ S := Finset.mem_univ _
  have hrest :
      ∑ a ∈ S.erase ∅, (incidenceFiber T a).card =
        ∑ a ∈ S.erase ∅, (incidenceFiber U a).card := by
    apply Finset.sum_congr rfl
    intro a ha
    have hane : a ≠ (∅ : Mask) := (Finset.mem_erase.mp ha).1
    have hpos : 0 < a.card := by
      rw [Finset.card_pos]
      exact Finset.nonempty_iff_ne_empty.mpr hane
    by_cases htwo : 2 ≤ a.card
    · exact incidenceFiber_card_eq_of_two_le T U hT hU hFamily a htwo
    · have hone : a.card = 1 := by omega
      exact incidenceFiber_card_eq_of_card_one T U hT hU hFamily a hone
  have hsumT := sum_incidenceFiber_univ T
  have hsumU := sum_incidenceFiber_univ U
  have hsplitT := S.sum_erase_add
    (fun a => (incidenceFiber T a).card) hmem
  have hsplitU := S.sum_erase_add
    (fun a => (incidenceFiber U a).card) hmem
  change (∑ a ∈ S, (incidenceFiber T a).card) = Fintype.card V at hsumT
  change (∑ a ∈ S, (incidenceFiber U a).card) = Fintype.card V at hsumU
  omega

theorem incidenceFiber_card_eq
    (T U : Block → Finset V)
    (hT : IsLinearTripleFamily T) (hU : IsLinearTripleFamily U)
    (hFamily : sharedFamilyOf T = sharedFamilyOf U)
    (m : Mask) :
    (incidenceFiber T m).card = (incidenceFiber U m).card := by
  by_cases htwo : 2 ≤ m.card
  · exact incidenceFiber_card_eq_of_two_le T U hT hU hFamily m htwo
  · by_cases hzero : m.card = 0
    · exact incidenceFiber_card_eq_of_card_zero T U hT hU hFamily m hzero
    · have hone : m.card = 1 := by omega
      exact incidenceFiber_card_eq_of_card_one T U hT hU hFamily m hone

/-- Equal shared-incidence families yield a vertex relabeling carrying one
ordered four-packing to the other. -/
theorem exists_block_preserving_equiv
    (T U : Block → Finset V)
    (hT : IsLinearTripleFamily T) (hU : IsLinearTripleFamily U)
    (hFamily : sharedFamilyOf T = sharedFamilyOf U) :
    ∃ e : Equiv.Perm V, ∀ i, (T i).map e.toEmbedding = U i := by
  classical
  let fiberEquiv : ∀ m : Mask,
      {v : V // incidence T v = m} ≃ {v : V // incidence U v = m} :=
    fun m => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      simpa [incidenceFiber] using incidenceFiber_card_eq T U hT hU hFamily m)
  let e : Equiv.Perm V := Equiv.ofFiberEquiv fiberEquiv
  refine ⟨e, ?_⟩
  intro i
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_map.mp hw
    rw [← hvw]
    change e v ∈ U i
    rw [← mem_incidence_iff U (e v) i]
    rw [Equiv.ofFiberEquiv_map fiberEquiv]
    exact (mem_incidence_iff T v i).mpr hv
  · intro hw
    let v := e.symm w
    apply Finset.mem_map.mpr
    refine ⟨v, ?_, e.apply_symm_apply w⟩
    have heq : e v = w := e.apply_symm_apply w
    have hvU : e v ∈ U i := by simpa [heq] using hw
    have hmask := Equiv.ofFiberEquiv_map fiberEquiv v
    rw [← mem_incidence_iff T v i, ← hmask]
    exact (mem_incidence_iff U (e v) i).mpr hvU

end TuzaRankFour.PackingClassification
