import TuzaRankFour.Certificates.Semantic.Order08Skeleton03Validity
import TuzaRankFour.Certificates.Semantic.Order08Skeleton03Formula00
import TuzaRankFour.Certificates.Segmented.Order08Skeleton03.All

namespace TuzaRankFour.Certificates.Semantic.Order08Skeleton03

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.FiniteEncoding
open TuzaRankFour.SemanticEncoding

theorem no_counterexample (G : SimpleGraph (Fin 8))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 8, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles 8)[i]? = some t ∧
        triangleFinset t ∈ G.triangles)
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  let v := graphValuation G
  have hBaseConditions : BaseConditions 8 v markedPacking :=
    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked
  have hCutConditions : CutConditions 8 v :=
    graphValuation_cutConditions G hν hτ
  have hBase : v.satisfies_fmla (baseFormula 8 markedPacking) :=
    satisfies_baseFormula hBaseConditions
  have hChunk0 : v.satisfies_fmla formulaChunk0 := by
    rw [formulaChunk0_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 0 264
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk0_valid)
  have hChunk1 : v.satisfies_fmla formulaChunk1 := by
    rw [formulaChunk1_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 264 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk1_valid)
  have hFormula : v.satisfies_fmla TuzaRankFour.Certificates.Segmented.Order08Skeleton03.formula := by
    exact satisfies_fmla_append (hChunk0) (hChunk1)
  exact TuzaRankFour.Certificates.Segmented.Order08Skeleton03.refutation v hFormula

end TuzaRankFour.Certificates.Semantic.Order08Skeleton03
