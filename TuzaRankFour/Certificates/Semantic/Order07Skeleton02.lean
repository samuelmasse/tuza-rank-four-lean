import TuzaRankFour.Certificates.Semantic.Order07Skeleton02Validity
import TuzaRankFour.Certificates.Semantic.Order07Skeleton02Formula00
import TuzaRankFour.Certificates.Segmented.Order07Skeleton02.All

namespace TuzaRankFour.Certificates.Semantic.Order07Skeleton02

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.FiniteEncoding
open TuzaRankFour.SemanticEncoding

theorem no_counterexample (G : SimpleGraph (Fin 7))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 7, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles 7)[i]? = some t ∧
        triangleFinset t ∈ G.triangles)
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  let v := graphValuation G
  have hBaseConditions : BaseConditions 7 v markedPacking :=
    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked
  have hCutConditions : CutConditions 7 v :=
    graphValuation_cutConditions G hν hτ
  have hBase : v.satisfies_fmla (baseFormula 7 markedPacking) :=
    satisfies_baseFormula hBaseConditions
  have hChunk0 : v.satisfies_fmla formulaChunk0 := by
    rw [formulaChunk0_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 0 172
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk0_valid)
  have hFormula : v.satisfies_fmla TuzaRankFour.Certificates.Segmented.Order07Skeleton02.formula := by
    exact hChunk0
  exact TuzaRankFour.Certificates.Segmented.Order07Skeleton02.refutation v hFormula

end TuzaRankFour.Certificates.Semantic.Order07Skeleton02
