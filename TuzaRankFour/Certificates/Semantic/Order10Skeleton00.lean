import TuzaRankFour.Certificates.Semantic.Order10Skeleton00Validity
import TuzaRankFour.Certificates.Semantic.Order10Skeleton00Formula00
import TuzaRankFour.Certificates.Segmented.Order10Skeleton00.All

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton00

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.FiniteEncoding
open TuzaRankFour.SemanticEncoding

theorem no_counterexample (G : SimpleGraph (Fin 10))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 10, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles 10)[i]? = some t ∧
        triangleFinset t ∈ G.triangles)
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  let v := graphValuation G
  have hBaseConditions : BaseConditions 10 v markedPacking :=
    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked
  have hCutConditions : CutConditions 10 v :=
    graphValuation_cutConditions G hν hτ
  have hBase : v.satisfies_fmla (baseFormula 10 markedPacking) :=
    satisfies_baseFormula hBaseConditions
  have hChunk0 : v.satisfies_fmla formulaChunk0 := by
    rw [formulaChunk0_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 0 396
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk0_valid)
  have hChunk1 : v.satisfies_fmla formulaChunk1 := by
    rw [formulaChunk1_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 396 143
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk1_valid)
  have hChunk2 : v.satisfies_fmla formulaChunk2 := by
    rw [formulaChunk2_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk2_valid)
  have hChunk3 : v.satisfies_fmla formulaChunk3 := by
    rw [formulaChunk3_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk3_valid)
  have hFormula : v.satisfies_fmla TuzaRankFour.Certificates.Segmented.Order10Skeleton00.formula := by
    exact satisfies_fmla_append (satisfies_fmla_append (hChunk0) (hChunk1)) (satisfies_fmla_append (hChunk2) (hChunk3))
  exact TuzaRankFour.Certificates.Segmented.Order10Skeleton00.refutation v hFormula

end TuzaRankFour.Certificates.Semantic.Order10Skeleton00
