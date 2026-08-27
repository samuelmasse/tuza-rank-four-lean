import Mathlib.Tactic

open Finset

example {V : Type*} [DecidableEq V]
    {p₁ p₂ p₃ s t : Finset V}
    (hp₁ : p₁.card = 3) (hp₂ : p₂.card = 3) (hp₃ : p₃.card = 3)
    (hs : s.card = 3) (ht : t.card = 3)
    (h₁₂ : (p₁ ∩ p₂).card ≤ 1)
    (h₂₃ : (p₂ ∩ p₃).card ≤ 1)
    (h₃₁ : (p₃ ∩ p₁).card ≤ 1)
    (hs₁ : 2 ≤ (p₁ ∩ s).card)
    (hs₂ : 2 ≤ (p₂ ∩ s).card)
    (hs₃ : 2 ≤ (p₃ ∩ s).card)
    (ht₁ : 2 ≤ (p₁ ∩ t).card)
    (ht₂ : 2 ≤ (p₂ ∩ t).card)
    (ht₃ : 2 ≤ (p₃ ∩ t).card) :
    s = t := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := s.card_eq_three.mp hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := t.card_eq_three.mp ht
  ext q
  simp only [mem_insert, mem_singleton]
  grind
