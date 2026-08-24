import TuzaRankFour.CaseDispatch
import TuzaRankFour.RankFourOrderBound

/-!
# Certified finite endpoint for the rank-four reduction
-/

namespace SimpleGraph

open TuzaRankFour.CaseDispatch

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- No supported rank-four strict counterexample exists on at most twelve
labelled vertices. -/
theorem no_supported_rank_four_counterexample_fin {n : Nat}
    (G : SimpleGraph (Fin n))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin n, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber)
    (hcard : n ≤ 12) : False := by
  have hsix : 6 ≤ n := by
    simpa using G.six_le_card_of_trianglePackingNumber_eq_four hν
  have hn : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
      n = 10 ∨ n = 11 ∨ n = 12 := by omega
  rcases hn with h | h | h | h | h | h | h
  · subst n
    exact no_rank_four_counterexample_six G hSupport hVertices hν hτ
  · subst n
    exact no_rank_four_counterexample_seven G hSupport hVertices hν hτ
  · subst n
    exact no_rank_four_counterexample_eight G hSupport hVertices hν hτ
  · subst n
    exact no_rank_four_counterexample_nine G hSupport hVertices hν hτ
  · subst n
    exact no_rank_four_counterexample_ten G hSupport hVertices hν hτ
  · subst n
    exact no_rank_four_counterexample_eleven G hSupport hVertices hν hτ
  · subst n
    exact no_rank_four_counterexample_twelve G hSupport hVertices hν hτ

/-- Carrier-independent form of the certified twelve-vertex endpoint. -/
theorem no_supported_rank_four_counterexample
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : V, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber)
    (hcard : Fintype.card V ≤ 12) : False := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let H := G.map e.toEmbedding
  apply no_supported_rank_four_counterexample_fin H
  · change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  · change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  · change (G.map e.toEmbedding).trianglePackingNumber = 4
    rw [G.trianglePackingNumber_map_equiv e]
    exact hν
  · change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  · simpa using hcard

end SimpleGraph
