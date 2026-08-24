import TuzaRankFour.Parker
import TuzaRankFour.Reduction
import TuzaRankFour.K4Reduction
import TuzaRankFour.CrownReduction
import TuzaRankFour.RankFourReduction
import TuzaRankFour.PackingSaturation
import TuzaRankFour.VertexSplitting
import TuzaRankFour.KernelReduction
import TuzaRankFour.Discharge
import TuzaRankFour.ComponentBound
import TuzaRankFour.DischargeClassification
import TuzaRankFour.CrownExtraction
import TuzaRankFour.ResidualIndependence
import TuzaRankFour.Exchange
import TuzaRankFour.TransferLedger
import TuzaRankFour.ComponentTransfer
import TuzaRankFour.InternalResidual
import TuzaRankFour.GlobalDischarge
import TuzaRankFour.RankFourOrderBound
import TuzaRankFour.FiniteEncoding
import TuzaRankFour.FiniteEndpoint

/-!
# Tuza's conjecture for packing number at most four

This file is the integration point for the analytic reduction and the checked
finite endpoint.
-/

namespace SimpleGraph

/-- Proof-development counterpart of the advertised theorem. -/
theorem tuza_rank_four_proof {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hν : G.trianglePackingNumber ≤ 4) :
    G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber := by
  classical
  by_cases hsmall : G.trianglePackingNumber ≤ 3
  · exact G.tuza_of_trianglePackingNumber_le_three hsmall
  have hνeq : G.trianglePackingNumber = 4 := by omega
  by_contra hbound
  have hτ : 8 < G.triangleTransversalNumber := by omega
  let K := G.rankFourKernel
  have hνK : K.trianglePackingNumber = 4 := by
    simpa [K] using G.trianglePackingNumber_rankFourKernel.trans hνeq
  have hτK : 8 < K.triangleTransversalNumber := by
    have hle : G.triangleTransversalNumber ≤ K.triangleTransversalNumber := by
      simpa [K] using G.triangleTransversalNumber_le_rankFourKernel
    omega
  have hSupportK : K.triangleSupport = K := by
    simpa [K] using G.triangleSupport_rankFourKernel
  have hVerticesK : ∀ v, v ∈ K.triangleSupportVertices := by
    intro v
    simpa [K] using G.mem_triangleSupportVertices_rankFourKernel v
  have hcardK : Fintype.card G.triangleSupport.SplitVertex ≤ 12 :=
    G.rankFourKernel_card_le_twelve hνeq hτ
  exact no_supported_rank_four_counterexample K hSupportK hVerticesK
    hνK hτK hcardK

end SimpleGraph
