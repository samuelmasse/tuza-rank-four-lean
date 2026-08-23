import TuzaRankFour.Definitions

/-!
# Elementary facts about the packing number

These lemmas connect the finite `Finset.sup` definition of `ν(G)` to the
usual extremal characterization and discharge the rank-zero case.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V)

@[simp]
theorem isTrianglePacking_empty : G.IsTrianglePacking ∅ := by
  classical
  simp [IsTrianglePacking]

theorem isTrianglePacking_singleton {t : Finset V} (ht : t ∈ G.triangles) :
    G.IsTrianglePacking {t} := by
  classical
  simp [IsTrianglePacking, ht]

/-- Every triangle packing has cardinality at most `ν(G)`. -/
theorem card_le_trianglePackingNumber {P : Finset (Finset V)}
    (hP : G.IsTrianglePacking P) : P.card ≤ G.trianglePackingNumber := by
  classical
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hP

/-- The extremal definition of `ν(G)` has the expected universal property. -/
theorem trianglePackingNumber_le_iff {k : ℕ} :
    G.trianglePackingNumber ≤ k ↔
      ∀ P : Finset (Finset V), G.IsTrianglePacking P → P.card ≤ k := by
  classical
  constructor
  · intro h P hP
    exact (G.card_le_trianglePackingNumber hP).trans h
  · intro h
    rw [trianglePackingNumber]
    exact Finset.sup_le fun P hP ↦ h P (by simpa using hP)

/-- A graph has packing number zero exactly when it has no triangle. -/
theorem trianglePackingNumber_eq_zero_iff :
    G.trianglePackingNumber = 0 ↔ G.triangles = ∅ := by
  classical
  constructor
  · intro hν
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hcard := G.card_le_trianglePackingNumber (G.isTrianglePacking_singleton ht)
    simp [hν] at hcard
  · intro htri
    apply Nat.eq_zero_of_le_zero
    rw [G.trianglePackingNumber_le_iff]
    intro P hP
    have hsubset := hP.1
    rw [htri] at hsubset
    have : P = ∅ := Finset.subset_empty.mp hsubset
    simp [this]

/-- A maximum triangle packing exists on every finite graph. -/
theorem exists_max_trianglePacking :
    ∃ P : Finset (Finset V),
      G.IsTrianglePacking P ∧ P.card = G.trianglePackingNumber := by
  classical
  by_cases hν : G.trianglePackingNumber = 0
  · exact ⟨∅, G.isTrianglePacking_empty, by simp [hν]⟩
  · have hpos : 0 < G.trianglePackingNumber := Nat.pos_of_ne_zero hν
    have hle :
        G.trianglePackingNumber ≤
          (Finset.univ.filter G.IsTrianglePacking).sup Finset.card := by
      simp [trianglePackingNumber]
    obtain ⟨P, hPmem, hνP⟩ := (Finset.le_sup_iff hpos).mp hle
    have hP : G.IsTrianglePacking P := by simpa using hPmem
    refine ⟨P, hP, le_antisymm ?_ hνP⟩
    exact G.card_le_trianglePackingNumber hP

/-- The full edge set is always a triangle transversal. -/
theorem isTriangleTransversal_edges : G.IsTriangleTransversal G.edges := by
  classical
  constructor
  · exact Finset.Subset.rfl
  · intro t ht
    have ht' : G.IsNClique 3 t := by
      simpa [triangles] using ht
    obtain ⟨e, het, hecard⟩ :=
      Finset.exists_subset_card_eq (s := t) (n := 2) (by simp [ht'.card_eq])
    refine ⟨e, ?_, het⟩
    simp only [edges, mem_cliqueFinset_iff]
    refine ⟨ht'.isClique.subset ?_, hecard⟩
    simpa using het

/-- The set of attainable transversal cardinalities is nonempty. -/
theorem transversalCardSet_nonempty :
    {n : ℕ | ∃ C : Finset (Finset V),
      G.IsTriangleTransversal C ∧ C.card = n}.Nonempty := by
  exact ⟨G.edges.card, G.edges, G.isTriangleTransversal_edges, rfl⟩

/-- Every transversal bounds `τ(G)` from above. -/
theorem triangleTransversalNumber_le_card {C : Finset (Finset V)}
    (hC : G.IsTriangleTransversal C) :
    G.triangleTransversalNumber ≤ C.card := by
  apply Nat.sInf_le
  exact ⟨C, hC, rfl⟩

/-- A minimum triangle transversal exists on every finite graph. -/
theorem exists_min_triangleTransversal :
    ∃ C : Finset (Finset V),
      G.IsTriangleTransversal C ∧ C.card = G.triangleTransversalNumber := by
  exact Nat.sInf_mem G.transversalCardSet_nonempty

/-- The extremal definition of `τ(G)` has the expected existential property. -/
theorem triangleTransversalNumber_le_iff {k : ℕ} :
    G.triangleTransversalNumber ≤ k ↔
      ∃ C : Finset (Finset V), G.IsTriangleTransversal C ∧ C.card ≤ k := by
  constructor
  · intro h
    obtain ⟨C, hC, hcard⟩ := G.exists_min_triangleTransversal
    exact ⟨C, hC, hcard.trans_le h⟩
  · rintro ⟨C, hC, hcard⟩
    exact (G.triangleTransversalNumber_le_card hC).trans hcard

@[simp]
theorem isTriangleTransversal_empty_iff :
    G.IsTriangleTransversal ∅ ↔ G.triangles = ∅ := by
  classical
  simp [IsTriangleTransversal, Finset.eq_empty_iff_forall_notMem]

/-- Tuza's bound in the vacuous rank-zero case. -/
theorem exists_triangleTransversal_of_packingNumber_eq_zero
    (hν : G.trianglePackingNumber = 0) :
    ∃ C : Finset (Finset V),
      G.IsTriangleTransversal C ∧ C.card ≤ 2 * G.trianglePackingNumber := by
  refine ⟨∅, ?_, by simp [hν]⟩
  exact G.isTriangleTransversal_empty_iff.mpr
    (G.trianglePackingNumber_eq_zero_iff.mp hν)

end SimpleGraph
