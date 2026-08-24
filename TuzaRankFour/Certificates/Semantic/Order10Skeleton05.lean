import TuzaRankFour.Certificates.Semantic.Order10Skeleton05Validity
import TuzaRankFour.Certificates.Semantic.Order10Skeleton05Formula01
import TuzaRankFour.Certificates.Segmented.Order10Skeleton05.All

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton05

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
    · exact satisfies_fmla_drop_take hBase 0 281
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk0_valid)
  have hChunk1 : v.satisfies_fmla formulaChunk1 := by
    rw [formulaChunk1_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 281 258
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
  have hChunk4 : v.satisfies_fmla formulaChunk4 := by
    rw [formulaChunk4_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk4_valid)
  have hChunk5 : v.satisfies_fmla formulaChunk5 := by
    rw [formulaChunk5_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk5_valid)
  have hChunk6 : v.satisfies_fmla formulaChunk6 := by
    rw [formulaChunk6_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk6_valid)
  have hChunk7 : v.satisfies_fmla formulaChunk7 := by
    rw [formulaChunk7_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk7_valid)
  have hChunk8 : v.satisfies_fmla formulaChunk8 := by
    rw [formulaChunk8_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk8_valid)
  have hChunk9 : v.satisfies_fmla formulaChunk9 := by
    rw [formulaChunk9_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk9_valid)
  have hChunk10 : v.satisfies_fmla formulaChunk10 := by
    rw [formulaChunk10_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk10_valid)
  have hChunk11 : v.satisfies_fmla formulaChunk11 := by
    rw [formulaChunk11_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk11_valid)
  have hChunk12 : v.satisfies_fmla formulaChunk12 := by
    rw [formulaChunk12_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk12_valid)
  have hChunk13 : v.satisfies_fmla formulaChunk13 := by
    rw [formulaChunk13_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk13_valid)
  have hChunk14 : v.satisfies_fmla formulaChunk14 := by
    rw [formulaChunk14_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk14_valid)
  have hChunk15 : v.satisfies_fmla formulaChunk15 := by
    rw [formulaChunk15_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 539 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk15_valid)
  have hFormula : v.satisfies_fmla TuzaRankFour.Certificates.Segmented.Order10Skeleton05.formula := by
    exact satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (hChunk0) (hChunk1)) (satisfies_fmla_append (hChunk2) (hChunk3))) (satisfies_fmla_append (satisfies_fmla_append (hChunk4) (hChunk5)) (satisfies_fmla_append (hChunk6) (hChunk7)))) (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (hChunk8) (hChunk9)) (satisfies_fmla_append (hChunk10) (hChunk11))) (satisfies_fmla_append (satisfies_fmla_append (hChunk12) (hChunk13)) (satisfies_fmla_append (hChunk14) (hChunk15))))
  exact TuzaRankFour.Certificates.Segmented.Order10Skeleton05.refutation v hFormula

end TuzaRankFour.Certificates.Semantic.Order10Skeleton05
