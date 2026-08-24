import TuzaRankFour.GlobalDischarge

/-!
# The twelve-vertex rank-four kernel bound

This file specializes the analytic discharge to the canonical supported,
split-normal kernel of a hypothetical strict rank-four counterexample.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical kernel of a strict rank-four counterexample has at most
twelve vertices. -/
theorem rankFourKernel_card_le_twelve
    (G : SimpleGraph V)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) :
    Fintype.card G.triangleSupport.SplitVertex ≤ 12 := by
  classical
  let H := G.rankFourKernel
  obtain ⟨S, hS⟩ := H.exists_supportMaximalPacking
  have hνH : H.trianglePackingNumber = 4 := by
    simpa [H] using G.trianglePackingNumber_rankFourKernel.trans hν
  have hScard : S.card = 4 := hS.2.1.trans hνH
  have hNoK4 : ∀ Q : Finset G.triangleSupport.SplitVertex,
      ¬H.IsTriangleIsolatedK4 Q := by
    simpa [H] using G.rankFourKernel_no_triangleIsolatedK4 hν hτ
  have hNoCrown : ¬∃ K : H.FatHeadCrown, K.headEdges.Nonempty := by
    rintro ⟨K, hK⟩
    have hEmpty : K.headEdges = ∅ := by
      simpa [H] using G.rankFourKernel_no_fatHeadCrown hν hτ K
    exact (Finset.nonempty_iff_ne_empty.mp hK) hEmpty
  have hbound := H.fintype_card_le_three_mul_packing_card hS hNoK4
    (by simpa [H] using G.isSplitNormal_rankFourKernel)
    (by simpa [H] using G.triangleSupport_rankFourKernel)
    (by
      intro z
      simpa [H] using G.mem_triangleSupportVertices_rankFourKernel z)
    hNoCrown
  omega

end SimpleGraph
