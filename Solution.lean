import TuzaRankFour

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

namespace SimpleGraph

theorem tuza_rank_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hν : G.trianglePackingNumber ≤ 4) :
    G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber := by
  exact tuza_rank_four_proof G hν

end SimpleGraph

