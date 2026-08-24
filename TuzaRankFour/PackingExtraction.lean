import TuzaRankFour.CanonicalPacking
import TuzaRankFour.Packing

/-!
# Extracting and canonically labelling a maximum four-packing
-/

namespace SimpleGraph

open TuzaRankFour.PackingClassification

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph of packing number four contains four ordered, pairwise
edge-disjoint triangle blocks. -/
theorem exists_ordered_linear_four_packing (G : SimpleGraph V)
    (hν : G.trianglePackingNumber = 4) :
    ∃ T : Block → Finset V,
      IsLinearTripleFamily T ∧ ∀ i, T i ∈ G.triangles := by
  classical
  obtain ⟨P, hP, hPcard⟩ := G.exists_max_trianglePacking
  have hcard : P.card = 4 := hPcard.trans hν
  let index : Block ≃ {t : Finset V // t ∈ P} :=
    Fintype.equivOfCardEq (by simp [hcard])
  let T : Block → Finset V := fun i => (index i).val
  refine ⟨T, ?_, ?_⟩
  · constructor
    · intro i
      have htri : T i ∈ G.triangles := hP.1 (index i).property
      have hclique : G.IsNClique 3 (T i) := by
        simpa [triangles] using htri
      exact hclique.card_eq
    · intro i j hij
      have hne : T i ≠ T j := by
        intro h
        apply hij
        apply index.injective
        exact Subtype.ext h
      exact hP.2 (index i).property (index j).property hne
  · intro i
    exact hP.1 (index i).property

/-- Four pairwise edge-disjoint triangles require at least six vertices. -/
theorem six_le_card_of_trianglePackingNumber_eq_four (G : SimpleGraph V)
    (hν : G.trianglePackingNumber = 4) : 6 ≤ Fintype.card V := by
  obtain ⟨T, hT, hTriangles⟩ := G.exists_ordered_linear_four_packing hν
  obtain ⟨s, p, hClass⟩ :=
    classifySharedFamilies (sharedFamilyOf T) (sharedFamilyOf_valid T hT)
  let T' := reindex p T
  have hT' : IsLinearTripleFamily T' :=
    isLinearTripleFamily_reindex p T hT
  have hFamily : sharedFamilyOf T' = canonicalSharedFamily s := by
    rw [sharedFamilyOf_reindex]
    exact hClass
  calc
    6 ≤ canonicalOrder s := six_le_canonicalOrder s
    _ = requiredOrder (canonicalSharedFamily s) :=
      canonicalOrder_eq_requiredOrder s
    _ = requiredOrder (sharedFamilyOf T') := by rw [hFamily]
    _ ≤ Fintype.card V := requiredOrder_le_card T' hT'

/-- Canonicalize a graph's maximum four-packing at a fixed order. -/
theorem exists_canonical_four_packing_of_endpoint {n : Nat}
    (G : SimpleGraph (Fin n)) (hν : G.trianglePackingNumber = 4)
    (hCanonicalize : ∀ T : Block → Finset (Fin n), IsLinearTripleFamily T →
      ∃ s : Fin 16, ∃ p : Equiv.Perm Block, ∃ e : Equiv.Perm (Fin n),
        canonicalOrder s ≤ n ∧
          ∀ i, (reindex p T i).map e.toEmbedding = canonicalBlockFin n s i) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin n),
      canonicalOrder s ≤ n ∧
        ∀ i, canonicalBlockFin n s i ∈ (G.map e.toEmbedding).triangles := by
  classical
  obtain ⟨T, hT, hTriangles⟩ := G.exists_ordered_linear_four_packing hν
  obtain ⟨s, p, e, hfit, he⟩ := hCanonicalize T hT
  refine ⟨s, e, hfit, ?_⟩
  intro i
  rw [G.triangles_map_equiv e]
  apply Finset.mem_map.mpr
  refine ⟨reindex p T i, hTriangles (p.symm i), ?_⟩
  exact he i

theorem exists_canonical_four_packing_six
    (G : SimpleGraph (Fin 6)) (hν : G.trianglePackingNumber = 4) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin 6),
      canonicalOrder s ≤ 6 ∧
        ∀ i, canonicalBlockFin 6 s i ∈ (G.map e.toEmbedding).triangles :=
  G.exists_canonical_four_packing_of_endpoint hν canonicalize_six

theorem exists_canonical_four_packing_seven
    (G : SimpleGraph (Fin 7)) (hν : G.trianglePackingNumber = 4) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin 7),
      canonicalOrder s ≤ 7 ∧
        ∀ i, canonicalBlockFin 7 s i ∈ (G.map e.toEmbedding).triangles :=
  G.exists_canonical_four_packing_of_endpoint hν canonicalize_seven

theorem exists_canonical_four_packing_eight
    (G : SimpleGraph (Fin 8)) (hν : G.trianglePackingNumber = 4) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin 8),
      canonicalOrder s ≤ 8 ∧
        ∀ i, canonicalBlockFin 8 s i ∈ (G.map e.toEmbedding).triangles :=
  G.exists_canonical_four_packing_of_endpoint hν canonicalize_eight

theorem exists_canonical_four_packing_nine
    (G : SimpleGraph (Fin 9)) (hν : G.trianglePackingNumber = 4) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin 9),
      canonicalOrder s ≤ 9 ∧
        ∀ i, canonicalBlockFin 9 s i ∈ (G.map e.toEmbedding).triangles :=
  G.exists_canonical_four_packing_of_endpoint hν canonicalize_nine

theorem exists_canonical_four_packing_ten
    (G : SimpleGraph (Fin 10)) (hν : G.trianglePackingNumber = 4) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin 10),
      canonicalOrder s ≤ 10 ∧
        ∀ i, canonicalBlockFin 10 s i ∈ (G.map e.toEmbedding).triangles :=
  G.exists_canonical_four_packing_of_endpoint hν canonicalize_ten

theorem exists_canonical_four_packing_eleven
    (G : SimpleGraph (Fin 11)) (hν : G.trianglePackingNumber = 4) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin 11),
      canonicalOrder s ≤ 11 ∧
        ∀ i, canonicalBlockFin 11 s i ∈ (G.map e.toEmbedding).triangles :=
  G.exists_canonical_four_packing_of_endpoint hν canonicalize_eleven

theorem exists_canonical_four_packing_twelve
    (G : SimpleGraph (Fin 12)) (hν : G.trianglePackingNumber = 4) :
    ∃ s : Fin 16, ∃ e : Equiv.Perm (Fin 12),
      canonicalOrder s ≤ 12 ∧
        ∀ i, canonicalBlockFin 12 s i ∈ (G.map e.toEmbedding).triangles :=
  G.exists_canonical_four_packing_of_endpoint hν canonicalize_twelve

end SimpleGraph
