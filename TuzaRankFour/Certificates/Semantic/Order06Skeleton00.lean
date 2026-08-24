import TuzaRankFour.Certificates.Semantic.Order06Skeleton00Validity
import TuzaRankFour.Certificates.Semantic.Order06Skeleton00Formula00
import TuzaRankFour.Certificates.Segmented.Order06Skeleton00.All

namespace TuzaRankFour.Certificates.Semantic.Order06Skeleton00

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.FiniteEncoding
open TuzaRankFour.SemanticEncoding

theorem no_counterexample (G : SimpleGraph (Fin 6))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 6, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles 6)[i]? = some t ∧
        triangleFinset t ∈ G.triangles)
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  let v := graphValuation G
  have hBaseConditions : BaseConditions 6 v markedPacking :=
    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked
  have hCutConditions : CutConditions 6 v :=
    graphValuation_cutConditions G hν hτ
  have hBase : v.satisfies_fmla (baseFormula 6 markedPacking) :=
    satisfies_baseFormula hBaseConditions
  have hChunk0 : v.satisfies_fmla formulaChunk0 := by
    rw [formulaChunk0_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 0 105
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk0_valid)
  have hFormula : v.satisfies_fmla TuzaRankFour.Certificates.Segmented.Order06Skeleton00.formula := by
    exact hChunk0
  exact TuzaRankFour.Certificates.Segmented.Order06Skeleton00.refutation v hFormula

end TuzaRankFour.Certificates.Semantic.Order06Skeleton00
