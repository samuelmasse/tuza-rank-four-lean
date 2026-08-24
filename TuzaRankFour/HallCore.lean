import Mathlib.Combinatorics.Hall.Basic

/-!
# A finite Hall-deficiency core

An inclusion-minimal deficient set on one side of a finite relation has a
matching from all of its neighbours back into the set.  This is the finite
combinatorial core of the fat-head crown extraction.
-/

namespace FiniteRelation

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- Forget the membership proofs in a finset of elements of a finite subtype. -/
noncomputable def values {γ : Type*} [DecidableEq γ] {s : Finset γ}
    (A : Finset s) : Finset γ := by
  classical
  exact A.map (Function.Embedding.subtype fun x : γ ↦ x ∈ s)

@[simp]
theorem mem_values_iff {γ : Type*} [DecidableEq γ] {s : Finset γ}
    {A : Finset s} {x : γ} :
    x ∈ values A ↔ ∃ a ∈ A, a.1 = x := by
  classical
  simp [values]

@[simp]
theorem card_values {γ : Type*} [DecidableEq γ] {s : Finset γ}
    (A : Finset s) : (values A).card = A.card := by
  classical
  exact Finset.card_map _

/-- The finite set of right neighbours of `A` under `r`. -/
noncomputable def neighbors (r : α → β → Prop) (A : Finset α) : Finset β := by
  classical
  exact Finset.univ.filter fun b ↦ ∃ a ∈ A, r a b

@[simp]
theorem mem_neighbors_iff (r : α → β → Prop) (A : Finset α) (b : β) :
    b ∈ neighbors r A ↔ ∃ a ∈ A, r a b := by
  classical
  simp [neighbors]

/-- A deficient family contains one whose cardinality is minimal among all
deficient families. -/
theorem exists_card_minimal_deficient (r : α → β → Prop)
    {A : Finset α} (hA : (neighbors r A).card < A.card) :
    ∃ C : Finset α,
      (neighbors r C).card < C.card ∧
      ∀ D : Finset α,
        (neighbors r D).card < D.card → C.card ≤ D.card := by
  classical
  let candidates := Finset.univ.powerset.filter fun C : Finset α ↦
    (neighbors r C).card < C.card
  have hA_mem : A ∈ candidates := by
    simp [candidates, hA]
  obtain ⟨C, hC_mem, hC_min⟩ :=
    Finset.exists_min_image candidates Finset.card ⟨A, hA_mem⟩
  refine ⟨C, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hC_mem).2
  · intro D hD
    exact hC_min D (by simp [candidates, hD])

/-- Every cardinality-minimal deficient family admits an injective matching
from all of its right neighbours back into the family. -/
theorem exists_injective_matching_back_of_card_minimal_deficient
    (r : α → β → Prop) (C : Finset α)
    (hCdef : (neighbors r C).card < C.card)
    (hCmin : ∀ D : Finset α,
      (neighbors r D).card < D.card → C.card ≤ D.card) :
    ∃ f : {b : β // b ∈ neighbors r C} → {a : α // a ∈ C},
      Function.Injective f ∧ ∀ b, r (f b).1 b.1 := by
  classical
  let H := neighbors r C
  let back : {b : β // b ∈ H} → {a : α // a ∈ C} → Prop :=
    fun b a ↦ r a.1 b.1
  have hHall : ∀ B : Finset {b : β // b ∈ H},
      B.card ≤
        (Finset.univ.filter fun a : {a : α // a ∈ C} ↦
          ∃ b ∈ B, back b a).card := by
    intro B
    let B₀ : Finset β := B.map (Function.Embedding.subtype fun b : β ↦ b ∈ H)
    let D : Finset α := C.filter fun a ↦ ∃ b ∈ B, r a b.1
    have hB₀card : B₀.card = B.card := by
      exact Finset.card_map _
    have hB₀sub : B₀ ⊆ H := by
      intro b hb
      simp only [B₀, Finset.mem_map] at hb
      obtain ⟨b', hb'B, rfl⟩ := hb
      exact b'.2
    have hDsub : D ⊆ C := Finset.filter_subset _ _
    have hDcard :
        (Finset.univ.filter fun a : {a : α // a ∈ C} ↦
          ∃ b ∈ B, back b a).card = D.card := by
      let source :=
        Finset.univ.filter fun a : {a : α // a ∈ C} ↦
          ∃ b ∈ B, back b a
      have hmap : source.map
          (Function.Embedding.subtype fun a : α ↦ a ∈ C) = D := by
        ext a
        simp [source, D, back, and_comm]
      have hcard := Finset.card_map
        (Function.Embedding.subtype fun a : α ↦ a ∈ C) (s := source)
      rw [hmap] at hcard
      exact hcard.symm
    by_contra hnot
    have hDltB : D.card < B.card := by
      rw [hDcard] at hnot
      omega
    have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
    have hDnonempty : D.Nonempty := by
      obtain ⟨b, hbB⟩ := hBnonempty
      have hbH : b.1 ∈ H := b.2
      obtain ⟨a, haC, hab⟩ := (mem_neighbors_iff r C b.1).mp hbH
      exact ⟨a, Finset.mem_filter.mpr
        ⟨haC, ⟨b, hbB, hab⟩⟩⟩
    let C' := C \ D
    have hNsub : neighbors r C' ⊆ H \ B₀ := by
      intro b hbN
      obtain ⟨a, haC', hab⟩ := (mem_neighbors_iff r C' b).mp hbN
      have haData := Finset.mem_sdiff.mp haC'
      apply Finset.mem_sdiff.mpr
      refine ⟨(mem_neighbors_iff r C b).mpr ⟨a, haData.1, hab⟩, ?_⟩
      intro hbB₀
      obtain ⟨b', hb'B, hb'eq⟩ := Finset.mem_map.mp hbB₀
      have hb'eqVal : b'.1 = b := hb'eq
      exact haData.2 (Finset.mem_filter.mpr
        ⟨haData.1, ⟨b', hb'B, by simpa [hb'eqVal] using hab⟩⟩)
    have hNcard : (neighbors r C').card ≤ (H \ B₀).card :=
      Finset.card_le_card hNsub
    have hB₀card_le : B₀.card ≤ H.card := Finset.card_le_card hB₀sub
    have hDcard_le : D.card ≤ C.card := Finset.card_le_card hDsub
    have hHdiff : (H \ B₀).card = H.card - B₀.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hB₀sub]
    have hCdiff : C'.card = C.card - D.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hDsub]
    have hC'def : (neighbors r C').card < C'.card := by
      change (neighbors r C').card < (C \ D).card
      change (neighbors r C').card ≤ (H \ B₀).card at hNcard
      rw [hHdiff, hB₀card] at hNcard
      rw [hCdiff]
      change H.card < C.card at hCdef
      omega
    have hminimal := hCmin C' hC'def
    rw [hCdiff] at hminimal
    have hDpos : 0 < D.card := Finset.card_pos.mpr hDnonempty
    omega
  have hMatching :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective back).mp hHall
  simpa [H, back] using hMatching

/-- Every deficient family contains a deficient core for which all right
neighbours can be matched injectively back to related vertices of the core. -/
theorem exists_deficient_core_with_injective_matching_back
    (r : α → β → Prop) {A : Finset α}
    (hA : (neighbors r A).card < A.card) :
    ∃ C : Finset α,
      (neighbors r C).card < C.card ∧
      ∃ f : {b : β // b ∈ neighbors r C} → {a : α // a ∈ C},
        Function.Injective f ∧ ∀ b, r (f b).1 b.1 := by
  classical
  obtain ⟨C, hCdef, hCmin⟩ := exists_card_minimal_deficient r hA
  exact ⟨C, hCdef,
    exists_injective_matching_back_of_card_minimal_deficient
      r C hCdef hCmin⟩

end FiniteRelation
