import TuzaRankFour.Certificates.FromBinaryLRAT
import TuzaRankFour.Packing

/-!
# Finite graph encoding

The finite endpoint numbers graph edges first and triples second, in the
lexicographic order produced by `itertools.combinations`.  This file defines
that order inside Lean and the corresponding propositional valuation of a
labelled graph.
-/

namespace TuzaRankFour.FiniteEncoding

/-- Ordered vertex pairs in lexicographic order. -/
def orderedEdges (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i < j).map fun j => (i, j)

/-- Ordered vertex triples in lexicographic order. -/
def orderedTriangles (n : Nat) : List (Fin n × Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i < j).flatMap fun j =>
      ((List.finRange n).filter fun k => j < k).map fun k => (i, j, k)

/-- The number of graph-edge variables preceding the triangle variables. -/
def edgeVariableCount (n : Nat) : Nat := (orderedEdges n).length

/-- A graph's valuation of the finite endpoint variables.  Variables beyond
the edge and triangle ranges are false. -/
def graphValuation {n : Nat} (G : SimpleGraph (Fin n)) : Sat.Valuation :=
  fun v =>
    match (orderedEdges n)[v]? with
    | some (i, j) => G.Adj i j
    | none =>
      match (orderedTriangles n)[v - edgeVariableCount n]? with
      | some (i, j, k) => G.Adj i j ∧ G.Adj i k ∧ G.Adj j k
      | none => False

/-- The order-three edge variables are exactly `01, 02, 12`. -/
theorem orderedEdges_three :
    orderedEdges 3 =
      [((0 : Fin 3), (1 : Fin 3)),
       ((0 : Fin 3), (2 : Fin 3)),
       ((1 : Fin 3), (2 : Fin 3))] := by
  decide

/-- The only order-three triple variable is `012`. -/
theorem orderedTriangles_three :
    orderedTriangles 3 =
      [((0 : Fin 3), (1 : Fin 3), (2 : Fin 3))] := by
  decide

theorem edgeVariableCount_three : edgeVariableCount 3 = 3 := by
  decide

/-- Smoke test for the first DIMACS variable. -/
theorem graphValuation_zero_iff_adj_zero_one
    (G : SimpleGraph (Fin 3)) :
    graphValuation G 0 ↔ G.Adj 0 1 := by
  unfold graphValuation
  rw [orderedEdges_three]
  rfl

/-- Smoke test for the first triangle variable, which follows the three edge
variables at zero-based index three. -/
theorem graphValuation_three_iff_triangle_zero_one_two
    (G : SimpleGraph (Fin 3)) :
    graphValuation G 3 ↔
      G.Adj 0 1 ∧ G.Adj 0 2 ∧ G.Adj 1 2 := by
  unfold graphValuation
  rw [orderedEdges_three, edgeVariableCount_three, orderedTriangles_three]
  rfl

end TuzaRankFour.FiniteEncoding
