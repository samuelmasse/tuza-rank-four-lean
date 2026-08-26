import TuzaRankFour.Certificates.Semantic.Order09Skeleton05Formula03
import TuzaRankFour.Certificates.Segmented.Order09Skeleton05.All

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton05

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.FiniteEncoding
open TuzaRankFour.SemanticEncoding

theorem no_counterexample (G : SimpleGraph (Fin 9))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 9, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles 9)[i]? = some t ∧
        triangleFinset t ∈ G.triangles)
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  let v := graphValuation G
  have hBaseConditions : BaseConditions 9 v markedPacking :=
    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked
  have hCutConditions : CutConditions 9 v :=
    graphValuation_cutConditions G hν hτ
  have hBase : v.satisfies_fmla (baseFormula 9 markedPacking) :=
    satisfies_baseFormula hBaseConditions
  have hChunk0 : v.satisfies_fmla formulaChunk0 := by
    rw [formulaChunk0_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 0 293
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk0_valid)
  have hChunk1 : v.satisfies_fmla formulaChunk1 := by
    rw [formulaChunk1_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 293 92
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk1_valid)
  have hChunk2 : v.satisfies_fmla formulaChunk2 := by
    rw [formulaChunk2_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 385 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk2_valid)
  have hChunk3 : v.satisfies_fmla formulaChunk3 := by
    rw [formulaChunk3_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 385 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk3_valid)
  have hChunk4 : v.satisfies_fmla formulaChunk4 := by
    rw [formulaChunk4_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 385 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk4_valid)
  have hChunk5 : v.satisfies_fmla formulaChunk5 := by
    rw [formulaChunk5_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 385 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk5_valid)
  have hChunk6 : v.satisfies_fmla formulaChunk6 := by
    rw [formulaChunk6_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 385 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk6_valid)
  have hChunk7 : v.satisfies_fmla formulaChunk7 := by
    rw [formulaChunk7_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 385 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk7_valid)
  have hFormula : v.satisfies_fmla TuzaRankFour.Certificates.Segmented.Order09Skeleton05.formula := by
    exact satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (hChunk0) (hChunk1)) (satisfies_fmla_append (hChunk2) (hChunk3))) (satisfies_fmla_append (satisfies_fmla_append (hChunk4) (hChunk5)) (satisfies_fmla_append (hChunk6) (hChunk7)))
  exact TuzaRankFour.Certificates.Segmented.Order09Skeleton05.refutation v hFormula

end TuzaRankFour.Certificates.Semantic.Order09Skeleton05
