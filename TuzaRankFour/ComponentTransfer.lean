import TuzaRankFour.TransferLedger
import TuzaRankFour.Exchange

/-!
# Componentwise transfer configuration

This file reconstructs the local configuration forced by a pretty-good
packing triangle.  It is the geometric input to the two-edge component
transfer.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Two distinct two-subsets of a three-set meet in exactly one vertex. -/
theorem card_inter_eq_one_of_distinct_powersetCard_two
    {t e f : Finset V} (htCard : t.card = 3)
    (he : e ∈ t.powersetCard 2) (hf : f ∈ t.powersetCard 2)
    (hef : e ≠ f) : (e ∩ f).card = 1 := by
  classical
  have heData := Finset.mem_powersetCard.mp he
  have hfData := Finset.mem_powersetCard.mp hf
  have hupper := card_inter_le_one_of_card_eq_two
    heData.2 hfData.2 hef
  have hunion := union_eq_of_mem_powersetCard_two_of_card_three
    htCard he hf hef
  have hcardUnion : (e ∪ f).card = 3 := by rw [hunion, htCard]
  rw [Finset.card_union] at hcardUnion
  omega

omit [Fintype V] in
/-- A two-subset of a three-set has a unique complementary vertex. -/
theorem exists_complement_vertex_of_powersetCard_two
    {t e : Finset V} (htCard : t.card = 3)
    (he : e ∈ t.powersetCard 2) :
    ∃ w, w ∉ e ∧ t = insert w e := by
  classical
  have heData := Finset.mem_powersetCard.mp he
  have hdiffCard : (t \ e).card = 1 := by
    rw [Finset.card_sdiff_of_subset heData.1, htCard, heData.2]
  obtain ⟨w, hwEq⟩ := Finset.card_eq_one.mp hdiffCard
  have hwDiff : w ∈ t \ e := by simp [hwEq]
  refine ⟨w, (Finset.mem_sdiff.mp hwDiff).2, ?_⟩
  apply Finset.Subset.antisymm
  · intro z hzt
    by_cases hze : z ∈ e
    · exact Finset.mem_insert_of_mem hze
    · have hzDiff : z ∈ t \ e := Finset.mem_sdiff.mpr ⟨hzt, hze⟩
      have : z = w := by simpa [hwEq] using hzDiff
      simpa [this]
  · exact Finset.insert_subset (Finset.mem_sdiff.mp hwDiff).1 heData.1

/-- A pretty-good triangle supplies labelled and unlabelled incident edges
`uv` and `uw`, with `uw` lying in a triangle `uwx` that avoids every labelled
packing edge. -/
theorem exists_prettyGood_transfer_configuration
    (G : SimpleGraph V) {S : Finset (Finset V)} {t : Finset V}
    (hS : G.IsTrianglePacking S)
    (htPretty : t ∈ G.prettyGoodPackingTriangles S) :
    ∃ u v w x : V,
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      x ≠ u ∧ x ≠ w ∧
      t = {u, v, w} ∧
      {u, v} ∈ G.labelledPackingEdges S ∧
      ∃ r : Finset V,
        r = {u, w, x} ∧ G.TriangleAvoidsPackingLabels S r := by
  classical
  have htGood := (G.mem_prettyGoodPackingTriangles_iff.mp htPretty).1
  have htS := (G.mem_goodPackingTriangles_iff.mp htGood).1
  have htCard : t.card = 3 := G.card_eq_three_of_mem_triangles (hS.1 htS)
  obtain ⟨l, hlSlice⟩ := (G.mem_goodPackingTriangles_iff.mp htGood).2
  have hlData := Finset.mem_inter.mp hlSlice
  obtain ⟨e, heT, heNotLabelled, r, hrAvoids, heSubR⟩ :=
    G.exists_avoiding_triangle_on_unlabelled_edge_of_prettyGood htPretty
  have hel : e ≠ l := fun hel ↦ heNotLabelled (hel ▸ hlData.2)
  have hinterCard : (e ∩ l).card = 1 :=
    card_inter_eq_one_of_distinct_powersetCard_two htCard heT hlData.1 hel
  obtain ⟨u, huInterEq⟩ := Finset.card_eq_one.mp hinterCard
  have huInter : u ∈ e ∩ l := by simp [huInterEq]
  have hue : u ∈ e := (Finset.mem_inter.mp huInter).1
  have hul : u ∈ l := (Finset.mem_inter.mp huInter).2
  have hlCard : l.card = 2 := (Finset.mem_powersetCard.mp hlData.1).2
  have heCard : e.card = 2 := (Finset.mem_powersetCard.mp heT).2
  have hlEraseCard : (l.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hul, hlCard]
  have heEraseCard : (e.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hue, heCard]
  obtain ⟨v, hvEraseEq⟩ := Finset.card_eq_one.mp hlEraseCard
  obtain ⟨w, hwEraseEq⟩ := Finset.card_eq_one.mp heEraseCard
  have hvl : v ∈ l := by
    have : v ∈ l.erase u := by simp [hvEraseEq]
    exact Finset.mem_of_mem_erase this
  have hwE : w ∈ e := by
    have : w ∈ e.erase u := by simp [hwEraseEq]
    exact Finset.mem_of_mem_erase this
  have huv : u ≠ v := by
    have : v ∈ l.erase u := by simp [hvEraseEq]
    exact (Finset.mem_erase.mp this).1.symm
  have huw : u ≠ w := by
    have : w ∈ e.erase u := by simp [hwEraseEq]
    exact (Finset.mem_erase.mp this).1.symm
  have hlEq : l = {u, v} := by
    rw [← Finset.insert_erase hul, hvEraseEq]
  have heEq : e = {u, w} := by
    rw [← Finset.insert_erase hue, hwEraseEq]
  have hvw : v ≠ w := by
    intro hvw
    subst w
    apply hel
    rw [hlEq, heEq]
  have htEq : t = {u, v, w} := by
    have hunion := union_eq_of_mem_powersetCard_two_of_card_three
      htCard heT hlData.1 hel
    rw [← hunion, hlEq, heEq]
    ext z
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hrCard : r.card = 3 := G.card_eq_three_of_mem_triangles hrAvoids.1
  have heR : e ∈ r.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨heSubR, heCard⟩
  obtain ⟨x, hxNotE, hrEqInsert⟩ :=
    exists_complement_vertex_of_powersetCard_two hrCard heR
  have hxu : x ≠ u := fun h ↦ hxNotE (h ▸ hue)
  have hxw : x ≠ w := fun h ↦ hxNotE (h ▸ hwE)
  have hrEq : r = {u, w, x} := by
    rw [hrEqInsert, heEq]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  exact ⟨u, v, w, x, huv, huw, hvw, hxu, hxw, htEq,
    by simpa [hlEq] using hlData.2, r, hrEq, hrAvoids⟩

end SimpleGraph
