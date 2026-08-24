import TuzaRankFour.PackingIncidence

/-!
# Canonical labelled four-packings

The sixteen abstract incidence types are realized on the initial segment of
`Fin n` by the same labelled triangles used in the sixty-six frozen SAT
instances.
-/

namespace TuzaRankFour.PackingClassification

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Number of vertices used by each frozen skeleton. -/
def canonicalOrders : List Nat :=
  [6, 7, 7, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 11, 12]

def canonicalOrder (s : Fin 16) : Nat :=
  canonicalOrders.getD s.val 0

theorem canonicalOrder_eq_requiredOrder (s : Fin 16) :
    canonicalOrder s = requiredOrder (canonicalSharedFamily s) := by
  revert s
  decide

theorem six_le_canonicalOrder (s : Fin 16) : 6 ≤ canonicalOrder s := by
  revert s
  decide

/-- Partial conversion from a natural label to `Fin n`. -/
def finOfNat? (n v : Nat) : Option (Fin n) :=
  if h : v < n then some ⟨v, h⟩ else none

theorem finOfNat?_injective (n : Nat) (a a' : Nat) (b : Fin n)
    (ha : b ∈ finOfNat? n a) (ha' : b ∈ finOfNat? n a') : a = a' := by
  simp only [finOfNat?] at ha ha'
  split at ha
  · split at ha'
    · have hf := Option.some.inj (ha.trans ha'.symm)
      exact congrArg (fun x : Fin n => x.val) hf
    · simp at ha'
  · simp at ha

/-- Canonical block on `Fin n`; labels outside the ambient order are omitted.
The fitting lemmas below show this never truncates a selected skeleton. -/
def canonicalBlockFin (n : Nat) (s : Fin 16) (i : Block) : Finset (Fin n) :=
  (canonicalBlock s i).filterMap (finOfNat? n)
    (finOfNat?_injective n)

theorem canonicalEndpoint_six (s : Fin 16)
    (hfit : canonicalOrder s ≤ 6) :
    IsLinearTripleFamily (canonicalBlockFin 6 s) ∧
      sharedFamilyOf (canonicalBlockFin 6 s) = canonicalSharedFamily s := by
  revert s
  decide

theorem canonicalEndpoint_seven (s : Fin 16)
    (hfit : canonicalOrder s ≤ 7) :
    IsLinearTripleFamily (canonicalBlockFin 7 s) ∧
      sharedFamilyOf (canonicalBlockFin 7 s) = canonicalSharedFamily s := by
  revert s
  decide

theorem canonicalEndpoint_eight (s : Fin 16)
    (hfit : canonicalOrder s ≤ 8) :
    IsLinearTripleFamily (canonicalBlockFin 8 s) ∧
      sharedFamilyOf (canonicalBlockFin 8 s) = canonicalSharedFamily s := by
  revert s
  decide

theorem canonicalEndpoint_nine (s : Fin 16)
    (hfit : canonicalOrder s ≤ 9) :
    IsLinearTripleFamily (canonicalBlockFin 9 s) ∧
      sharedFamilyOf (canonicalBlockFin 9 s) = canonicalSharedFamily s := by
  revert s
  decide

theorem canonicalEndpoint_ten (s : Fin 16)
    (hfit : canonicalOrder s ≤ 10) :
    IsLinearTripleFamily (canonicalBlockFin 10 s) ∧
      sharedFamilyOf (canonicalBlockFin 10 s) = canonicalSharedFamily s := by
  revert s
  decide

theorem canonicalEndpoint_eleven (s : Fin 16)
    (hfit : canonicalOrder s ≤ 11) :
    IsLinearTripleFamily (canonicalBlockFin 11 s) ∧
      sharedFamilyOf (canonicalBlockFin 11 s) = canonicalSharedFamily s := by
  revert s
  decide

theorem canonicalEndpoint_twelve (s : Fin 16)
    (hfit : canonicalOrder s ≤ 12) :
    IsLinearTripleFamily (canonicalBlockFin 12 s) ∧
      sharedFamilyOf (canonicalBlockFin 12 s) = canonicalSharedFamily s := by
  revert s
  decide

/-- Abstract canonicalization theorem.  A fixed-order endpoint lemma supplies
the realization of every skeleton that fits that order. -/
theorem canonicalize_of_endpoint {n : Nat}
    (T : Block → Finset (Fin n)) (hT : IsLinearTripleFamily T)
    (hEndpoint : ∀ s : Fin 16, canonicalOrder s ≤ n →
      IsLinearTripleFamily (canonicalBlockFin n s) ∧
        sharedFamilyOf (canonicalBlockFin n s) = canonicalSharedFamily s) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin n),
      canonicalOrder s ≤ n ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin n s i := by
  obtain ⟨s, p, hClass⟩ :=
    classifySharedFamilies (sharedFamilyOf T) (sharedFamilyOf_valid T hT)
  let T' := reindex p T
  have hT' : IsLinearTripleFamily T' :=
    isLinearTripleFamily_reindex p T hT
  have hFamily : sharedFamilyOf T' = canonicalSharedFamily s := by
    rw [sharedFamilyOf_reindex]
    exact hClass
  have hfit : canonicalOrder s ≤ n := by
    calc
      canonicalOrder s = requiredOrder (canonicalSharedFamily s) :=
        canonicalOrder_eq_requiredOrder s
      _ = requiredOrder (sharedFamilyOf T') := by rw [hFamily]
      _ ≤ Fintype.card (Fin n) := requiredOrder_le_card T' hT'
      _ = n := Fintype.card_fin n
  obtain ⟨hU, hUFamily⟩ := hEndpoint s hfit
  obtain ⟨e, he⟩ :=
    exists_block_preserving_equiv T' (canonicalBlockFin n s)
      hT' hU (hFamily.trans hUFamily.symm)
  exact ⟨s, p, e, hfit, he⟩

theorem canonicalize_six (T : Block → Finset (Fin 6))
    (hT : IsLinearTripleFamily T) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin 6),
      canonicalOrder s ≤ 6 ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin 6 s i :=
  canonicalize_of_endpoint T hT canonicalEndpoint_six

theorem canonicalize_seven (T : Block → Finset (Fin 7))
    (hT : IsLinearTripleFamily T) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin 7),
      canonicalOrder s ≤ 7 ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin 7 s i :=
  canonicalize_of_endpoint T hT canonicalEndpoint_seven

theorem canonicalize_eight (T : Block → Finset (Fin 8))
    (hT : IsLinearTripleFamily T) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin 8),
      canonicalOrder s ≤ 8 ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin 8 s i :=
  canonicalize_of_endpoint T hT canonicalEndpoint_eight

theorem canonicalize_nine (T : Block → Finset (Fin 9))
    (hT : IsLinearTripleFamily T) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin 9),
      canonicalOrder s ≤ 9 ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin 9 s i :=
  canonicalize_of_endpoint T hT canonicalEndpoint_nine

theorem canonicalize_ten (T : Block → Finset (Fin 10))
    (hT : IsLinearTripleFamily T) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin 10),
      canonicalOrder s ≤ 10 ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin 10 s i :=
  canonicalize_of_endpoint T hT canonicalEndpoint_ten

theorem canonicalize_eleven (T : Block → Finset (Fin 11))
    (hT : IsLinearTripleFamily T) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin 11),
      canonicalOrder s ≤ 11 ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin 11 s i :=
  canonicalize_of_endpoint T hT canonicalEndpoint_eleven

theorem canonicalize_twelve (T : Block → Finset (Fin 12))
    (hT : IsLinearTripleFamily T) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin 12),
      canonicalOrder s ≤ 12 ∧
        ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin 12 s i :=
  canonicalize_of_endpoint T hT canonicalEndpoint_twelve

end TuzaRankFour.PackingClassification
