import TuzaRankFour.Discharge

/-!
# Reusable packing-exchange contradictions

The discharge repeatedly replaces two packed triangles by three explicitly
compatible graph triangles.  This file isolates the cardinality argument so
later local proofs need only verify the intersection conditions.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A maximum packing cannot admit two edge-disjoint triangles compatible
with every member left after one packed triangle is removed. -/
theorem false_of_two_for_one_exchange
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {t a b : Finset V} (htS : t ∈ S)
    (ha : a ∈ G.triangles) (hb : b ∈ G.triangles)
    (hab : (a ∩ b).card ≤ 1)
    (haR : ∀ ⦃q⦄, q ∈ S.erase t → (q ∩ a).card ≤ 1)
    (hbR : ∀ ⦃q⦄, q ∈ S.erase t → (q ∩ b).card ≤ 1) :
    False := by
  classical
  let R := S.erase t
  have hRpacking : G.IsTrianglePacking R :=
    hS.1.mono_family G (Finset.erase_subset _ _)
  have haPacking : G.IsTrianglePacking (insert a R) :=
    G.isTrianglePacking_insert hRpacking ha haR
  have hbCompat : ∀ ⦃q⦄, q ∈ insert a R → (q ∩ b).card ≤ 1 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqR
    · exact hab
    · exact hbR hqR
  have hPpacking : G.IsTrianglePacking (insert b (insert a R)) :=
    G.isTrianglePacking_insert haPacking hb hbCompat
  have haCard : a.card = 3 := G.card_eq_three_of_mem_triangles ha
  have hbCard : b.card = 3 := G.card_eq_three_of_mem_triangles hb
  have haNotR : a ∉ R := by
    intro haMem
    have hsmall := haR haMem
    rw [Finset.inter_self, haCard] at hsmall
    omega
  have hbNotR : b ∉ R := by
    intro hbMem
    have hsmall := hbR hbMem
    rw [Finset.inter_self, hbCard] at hsmall
    omega
  have hba : b ≠ a := by
    intro hEq
    subst b
    rw [Finset.inter_self, haCard] at hab
    omega
  have hbNot : b ∉ insert a R := by
    simpa [Finset.mem_insert, hba, hbNotR]
  have hcardR : R.card + 1 = S.card := by
    change (S.erase t).card + 1 = S.card
    rw [Finset.card_erase_of_mem htS]
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨t, htS⟩
    omega
  have hcardP : (insert b (insert a R)).card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem hbNot,
      Finset.card_insert_of_notMem haNotR]
    omega
  have hbound := G.card_le_trianglePackingNumber hPpacking
  rw [hcardP, ← hS.2.1] at hbound
  omega

/-- A support-maximal packing cannot admit three pairwise edge-disjoint
triangles compatible with every member left after two packed triangles are
removed. -/
theorem false_of_three_for_two_exchange
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S)
    {s t a b c : Finset V} (hsS : s ∈ S) (htS : t ∈ S) (hst : s ≠ t)
    (ha : a ∈ G.triangles) (hb : b ∈ G.triangles)
    (hc : c ∈ G.triangles)
    (hab : (a ∩ b).card ≤ 1) (hac : (a ∩ c).card ≤ 1)
    (hbc : (b ∩ c).card ≤ 1)
    (haR : ∀ ⦃q⦄, q ∈ (S.erase s).erase t → (q ∩ a).card ≤ 1)
    (hbR : ∀ ⦃q⦄, q ∈ (S.erase s).erase t → (q ∩ b).card ≤ 1)
    (hcR : ∀ ⦃q⦄, q ∈ (S.erase s).erase t → (q ∩ c).card ≤ 1) :
    False := by
  classical
  let R := (S.erase s).erase t
  have hRsub : R ⊆ S :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hRpacking : G.IsTrianglePacking R := hS.1.mono_family G hRsub
  have haPacking : G.IsTrianglePacking (insert a R) :=
    G.isTrianglePacking_insert hRpacking ha haR
  have hbCompat : ∀ ⦃q⦄, q ∈ insert a R → (q ∩ b).card ≤ 1 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqR
    · exact hab
    · exact hbR hqR
  have hbPacking : G.IsTrianglePacking (insert b (insert a R)) :=
    G.isTrianglePacking_insert haPacking hb hbCompat
  have hcCompat : ∀ ⦃q⦄, q ∈ insert b (insert a R) →
      (q ∩ c).card ≤ 1 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqRest
    · exact hbc
    · rcases Finset.mem_insert.mp hqRest with rfl | hqR
      · exact hac
      · exact hcR hqR
  have hPpacking : G.IsTrianglePacking
      (insert c (insert b (insert a R))) :=
    G.isTrianglePacking_insert hbPacking hc hcCompat
  have haCard : a.card = 3 := G.card_eq_three_of_mem_triangles ha
  have hbCard : b.card = 3 := G.card_eq_three_of_mem_triangles hb
  have hcCard : c.card = 3 := G.card_eq_three_of_mem_triangles hc
  have haNotR : a ∉ R := by
    intro haMem
    have hsmall := haR haMem
    rw [Finset.inter_self, haCard] at hsmall
    omega
  have hbNotR : b ∉ R := by
    intro hbMem
    have hsmall := hbR hbMem
    rw [Finset.inter_self, hbCard] at hsmall
    omega
  have hcNotR : c ∉ R := by
    intro hcMem
    have hsmall := hcR hcMem
    rw [Finset.inter_self, hcCard] at hsmall
    omega
  have hba : b ≠ a := by
    intro hEq
    subst b
    rw [Finset.inter_self, haCard] at hab
    omega
  have hca : c ≠ a := by
    intro hEq
    subst c
    rw [Finset.inter_self, haCard] at hac
    omega
  have hcb : c ≠ b := by
    intro hEq
    subst c
    rw [Finset.inter_self, hbCard] at hbc
    omega
  have hbNot : b ∉ insert a R := by
    simpa [Finset.mem_insert, hba, hbNotR]
  have hcNot : c ∉ insert b (insert a R) := by
    simp only [Finset.mem_insert]
    push Not
    exact ⟨hcb, hca, hcNotR⟩
  have htErase : t ∈ S.erase s := Finset.mem_erase.mpr ⟨hst.symm, htS⟩
  have hcardR : R.card + 2 = S.card := by
    change ((S.erase s).erase t).card + 2 = S.card
    rw [Finset.card_erase_of_mem htErase,
      Finset.card_erase_of_mem hsS]
    have hSlarge : 2 ≤ S.card := by
      have hne : s ∈ S.erase t := Finset.mem_erase.mpr ⟨hst, hsS⟩
      have := Finset.card_pos.mpr ⟨s, hne⟩
      rw [Finset.card_erase_of_mem htS] at this
      omega
    omega
  have hcardP : (insert c (insert b (insert a R))).card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem hcNot,
      Finset.card_insert_of_notMem hbNot,
      Finset.card_insert_of_notMem haNotR]
    omega
  have hbound := G.card_le_trianglePackingNumber hPpacking
  rw [hcardP, ← hS.2.1] at hbound
  omega

end SimpleGraph
