import TuzaRankFour.Nonconstructive.Definitions

/-!
# Exact-rank reducer lift

This module proves the generic induction step used by every local blocker in
the nonconstructive route.  It has no rank-four or finite-certificate input.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A transversal of the residual graph lifts by union with the deleted
source edges.  This is the same-source cover transport used by every blocker
argument. -/
theorem isTriangleTransversal_union_deleteEdgeFinset
    (G : SimpleGraph V) {C D : Finset (Finset V)}
    (hC : C ⊆ G.edges)
    (hD : (G.deleteEdgeFinset C).IsTriangleTransversal D) :
    G.IsTriangleTransversal (C ∪ D) := by
  classical
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with heC | heD
    · exact hC heC
    · exact G.edges_deleteEdgeFinset_subset C (hD.1 heD)
  · intro t ht
    by_cases htResidual : t ∈ (G.deleteEdgeFinset C).triangles
    · obtain ⟨e, heD, het⟩ := hD.2 htResidual
      exact ⟨e, Finset.mem_union_right C heD, het⟩
    · have hhit : ∃ e ∈ C, e ⊆ t := by
        by_contra hnone
        push Not at hnone
        exact htResidual
          (G.mem_triangles_deleteEdgeFinset_of_forall_not_subset C ht hnone)
      obtain ⟨e, heC, het⟩ := hhit
      exact ⟨e, Finset.mem_union_left D heC, het⟩

/-- The numerical Tuza inequality lifts across any exact-rank blocker whose
edge cost is at most twice its exact damage. -/
theorem IsExactRankBlocker.satisfiesTuza_of_residual
    {G : SimpleGraph V} {C : Finset (Finset V)} {d : ℕ}
    (hBlocker : G.IsExactRankBlocker C d)
    (hCard : C.card ≤ 2 * d)
    (hResidual : (G.deleteEdgeFinset C).SatisfiesTuza) :
    G.SatisfiesTuza := by
  obtain ⟨D, hD, hDcard⟩ :=
    (G.deleteEdgeFinset C).triangleTransversalNumber_le_iff.mp hResidual
  rw [SatisfiesTuza]
  apply G.triangleTransversalNumber_le_iff.mpr
  refine ⟨C ∪ D,
    G.isTriangleTransversal_union_deleteEdgeFinset hBlocker.edges_subset hD,
    ?_⟩
  calc
    (C ∪ D).card ≤ C.card + D.card := Finset.card_union_le C D
    _ ≤ 2 * d + 2 * (G.deleteEdgeFinset C).trianglePackingNumber :=
      Nat.add_le_add hCard hDcard
    _ = 2 * ((G.deleteEdgeFinset C).trianglePackingNumber + d) := by omega
    _ = 2 * G.trianglePackingNumber := by rw [hBlocker.rank_eq]

/-- A packaged positive reducer performs the generic Tuza induction step. -/
theorem IsTuzaReducer.satisfiesTuza_of_residual
    {G : SimpleGraph V} {C : Finset (Finset V)} {d : ℕ}
    (hReducer : G.IsTuzaReducer C d)
    (hResidual : (G.deleteEdgeFinset C).SatisfiesTuza) :
    G.SatisfiesTuza :=
  hReducer.toIsExactRankBlocker.satisfiesTuza_of_residual
    hReducer.card_le hResidual

/-- The generic reducer implication in explicit cover form. -/
theorem IsExactRankBlocker.exists_triangleTransversal_of_residual
    {G : SimpleGraph V} {C : Finset (Finset V)} {d : ℕ}
    (hBlocker : G.IsExactRankBlocker C d)
    (hCard : C.card ≤ 2 * d)
    {D : Finset (Finset V)}
    (hD : (G.deleteEdgeFinset C).IsTriangleTransversal D)
    (hDcard : D.card ≤
      2 * (G.deleteEdgeFinset C).trianglePackingNumber) :
    ∃ E : Finset (Finset V),
      G.IsTriangleTransversal E ∧ E.card ≤ 2 * G.trianglePackingNumber := by
  refine ⟨C ∪ D,
    G.isTriangleTransversal_union_deleteEdgeFinset hBlocker.edges_subset hD,
    ?_⟩
  calc
    (C ∪ D).card ≤ C.card + D.card := Finset.card_union_le C D
    _ ≤ 2 * d + 2 * (G.deleteEdgeFinset C).trianglePackingNumber :=
      Nat.add_le_add hCard hDcard
    _ = 2 * ((G.deleteEdgeFinset C).trianglePackingNumber + d) := by omega
    _ = 2 * G.trianglePackingNumber := by rw [hBlocker.rank_eq]

/-- Rank zero is the base case for reducer induction. -/
theorem satisfiesTuza_of_trianglePackingNumber_eq_zero
    (G : SimpleGraph V) (hZero : G.trianglePackingNumber = 0) :
    G.SatisfiesTuza := by
  rw [SatisfiesTuza]
  obtain ⟨C, hC, hCard⟩ :=
    G.exists_triangleTransversal_of_packingNumber_eq_zero hZero
  exact G.triangleTransversalNumber_le_iff.mpr ⟨C, hC, hCard⟩

/-- Conditional all-rank theorem on one finite carrier: if every positive-rank
graph admits a positive strength-two exact-rank reducer, then every graph on
that carrier satisfies Tuza.

The hypothesis is intentionally exposed.  Formalizing a contact theorem as an
inhabitant of `HasUnavoidableTuzaReduction V` is the remaining graph-theoretic
obligation; this theorem contributes only the well-founded rank induction. -/
theorem satisfiesTuza_of_unavoidableTuzaReduction
    (hReduce : HasUnavoidableTuzaReduction V) :
    ∀ G : SimpleGraph V, G.SatisfiesTuza := by
  intro G
  generalize hRank : G.trianglePackingNumber = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hZero : n = 0
      · apply G.satisfiesTuza_of_trianglePackingNumber_eq_zero
        exact hRank.trans hZero
      · have hPos : 0 < G.trianglePackingNumber := by omega
        obtain ⟨C, d, hReducer⟩ := hReduce G hPos
        have hRankDrop := hReducer.rank_eq
        have hDamagePos := hReducer.damage_pos
        have hResidualRank :
            (G.deleteEdgeFinset C).trianglePackingNumber < n := by
          omega
        have hResidualTuza :
            (G.deleteEdgeFinset C).SatisfiesTuza :=
          ih _ hResidualRank (G.deleteEdgeFinset C) rfl
        exact hReducer.satisfiesTuza_of_residual hResidualTuza

end SimpleGraph
