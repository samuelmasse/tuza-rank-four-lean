import Mathlib.Tactic
import TuzaRankFour.CrownReduction
import TuzaRankFour.K4Reduction

/-!
# Counterexample reductions at packing rank four

Parker's rank-three theorem and the exact offset lemmas exclude the two
reducible configurations used before the discharging argument.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- A strict rank-four counterexample contains no triangle-isolated copy of
`K₄`. -/
theorem no_triangleIsolatedK4_of_rank_four_counterexample
    (hν : G.trianglePackingNumber = 4)
    (hτ : 2 * G.trianglePackingNumber < G.triangleTransversalNumber) :
    ¬∃ Q : Finset V, G.IsTriangleIsolatedK4 Q := by
  rintro ⟨Q, hQ⟩
  let G' := G.deleteEdgesWithin Q
  have hνOffset := G.trianglePackingNumber_eq_deleteEdgesWithin_add_one hQ
  have hτOffset := G.triangleTransversalNumber_eq_deleteEdgesWithin_add_two hQ
  have hν' : G'.trianglePackingNumber ≤ 3 := by
    change (G.deleteEdgesWithin Q).trianglePackingNumber ≤ 3
    omega
  have hparker := G'.tuza_of_trianglePackingNumber_le_three hν'
  change G'.triangleTransversalNumber ≤ 2 * G'.trianglePackingNumber at hparker
  change G.trianglePackingNumber =
      G'.trianglePackingNumber + 1 at hνOffset
  change G.triangleTransversalNumber =
      G'.triangleTransversalNumber + 2 at hτOffset
  omega

/-- A strict rank-four counterexample contains no fat-head crown with a
nonempty head. -/
theorem no_nonempty_fatHeadCrown_of_rank_four_counterexample
    (hν : G.trianglePackingNumber = 4)
    (hτ : 2 * G.trianglePackingNumber < G.triangleTransversalNumber) :
    ¬∃ K : G.FatHeadCrown, K.headEdges.Nonempty := by
  rintro ⟨K, hK⟩
  have hhead : 0 < K.headEdges.card := Finset.card_pos.mpr hK
  have hνOffset := K.trianglePackingNumber_eq_residual_add_card
  have hτOffset := K.triangleTransversalNumber_eq_residual_add_card
  have hν' : K.residual.trianglePackingNumber ≤ 3 := by omega
  have hparker := K.residual.tuza_of_trianglePackingNumber_le_three hν'
  omega

end SimpleGraph
