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
  sorry

end SimpleGraph
