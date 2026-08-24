import TuzaRankFour.Certificates.Semantic.Order12Skeleton03Validity
import TuzaRankFour.Certificates.Semantic.Order12Skeleton03Formula03
import TuzaRankFour.Certificates.Segmented.Order12Skeleton03.All

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton03

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.FiniteEncoding
open TuzaRankFour.SemanticEncoding

theorem no_counterexample (G : SimpleGraph (Fin 12))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 12, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles 12)[i]? = some t ∧
        triangleFinset t ∈ G.triangles)
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  let v := graphValuation G
  have hBaseConditions : BaseConditions 12 v markedPacking :=
    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked
  have hCutConditions : CutConditions 12 v :=
    graphValuation_cutConditions G hν hτ
  have hBase : v.satisfies_fmla (baseFormula 12 markedPacking) :=
    satisfies_baseFormula hBaseConditions
  have hChunk0 : v.satisfies_fmla formulaChunk0 := by
    rw [formulaChunk0_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 0 329
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk0_valid)
  have hChunk1 : v.satisfies_fmla formulaChunk1 := by
    rw [formulaChunk1_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 329 329
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk1_valid)
  have hChunk2 : v.satisfies_fmla formulaChunk2 := by
    rw [formulaChunk2_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 658 304
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk2_valid)
  have hChunk3 : v.satisfies_fmla formulaChunk3 := by
    rw [formulaChunk3_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk3_valid)
  have hChunk4 : v.satisfies_fmla formulaChunk4 := by
    rw [formulaChunk4_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk4_valid)
  have hChunk5 : v.satisfies_fmla formulaChunk5 := by
    rw [formulaChunk5_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk5_valid)
  have hChunk6 : v.satisfies_fmla formulaChunk6 := by
    rw [formulaChunk6_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk6_valid)
  have hChunk7 : v.satisfies_fmla formulaChunk7 := by
    rw [formulaChunk7_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk7_valid)
  have hChunk8 : v.satisfies_fmla formulaChunk8 := by
    rw [formulaChunk8_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk8_valid)
  have hChunk9 : v.satisfies_fmla formulaChunk9 := by
    rw [formulaChunk9_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk9_valid)
  have hChunk10 : v.satisfies_fmla formulaChunk10 := by
    rw [formulaChunk10_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk10_valid)
  have hChunk11 : v.satisfies_fmla formulaChunk11 := by
    rw [formulaChunk11_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk11_valid)
  have hChunk12 : v.satisfies_fmla formulaChunk12 := by
    rw [formulaChunk12_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk12_valid)
  have hChunk13 : v.satisfies_fmla formulaChunk13 := by
    rw [formulaChunk13_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk13_valid)
  have hChunk14 : v.satisfies_fmla formulaChunk14 := by
    rw [formulaChunk14_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk14_valid)
  have hChunk15 : v.satisfies_fmla formulaChunk15 := by
    rw [formulaChunk15_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk15_valid)
  have hChunk16 : v.satisfies_fmla formulaChunk16 := by
    rw [formulaChunk16_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk16_valid)
  have hChunk17 : v.satisfies_fmla formulaChunk17 := by
    rw [formulaChunk17_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk17_valid)
  have hChunk18 : v.satisfies_fmla formulaChunk18 := by
    rw [formulaChunk18_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk18_valid)
  have hChunk19 : v.satisfies_fmla formulaChunk19 := by
    rw [formulaChunk19_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk19_valid)
  have hChunk20 : v.satisfies_fmla formulaChunk20 := by
    rw [formulaChunk20_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk20_valid)
  have hChunk21 : v.satisfies_fmla formulaChunk21 := by
    rw [formulaChunk21_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk21_valid)
  have hChunk22 : v.satisfies_fmla formulaChunk22 := by
    rw [formulaChunk22_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk22_valid)
  have hChunk23 : v.satisfies_fmla formulaChunk23 := by
    rw [formulaChunk23_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk23_valid)
  have hChunk24 : v.satisfies_fmla formulaChunk24 := by
    rw [formulaChunk24_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk24_valid)
  have hChunk25 : v.satisfies_fmla formulaChunk25 := by
    rw [formulaChunk25_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk25_valid)
  have hChunk26 : v.satisfies_fmla formulaChunk26 := by
    rw [formulaChunk26_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk26_valid)
  have hChunk27 : v.satisfies_fmla formulaChunk27 := by
    rw [formulaChunk27_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk27_valid)
  have hChunk28 : v.satisfies_fmla formulaChunk28 := by
    rw [formulaChunk28_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk28_valid)
  have hChunk29 : v.satisfies_fmla formulaChunk29 := by
    rw [formulaChunk29_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk29_valid)
  have hChunk30 : v.satisfies_fmla formulaChunk30 := by
    rw [formulaChunk30_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk30_valid)
  have hChunk31 : v.satisfies_fmla formulaChunk31 := by
    rw [formulaChunk31_eq]
    apply satisfies_fmla_append
    · exact satisfies_fmla_drop_take hBase 962 0
    · exact satisfies_cutFormula hCutConditions _
        (valid_of_cutsValidBool cutChunk31_valid)
  have hFormula : v.satisfies_fmla TuzaRankFour.Certificates.Segmented.Order12Skeleton03.formula := by
    exact satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (hChunk0) (hChunk1)) (satisfies_fmla_append (hChunk2) (hChunk3))) (satisfies_fmla_append (satisfies_fmla_append (hChunk4) (hChunk5)) (satisfies_fmla_append (hChunk6) (hChunk7)))) (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (hChunk8) (hChunk9)) (satisfies_fmla_append (hChunk10) (hChunk11))) (satisfies_fmla_append (satisfies_fmla_append (hChunk12) (hChunk13)) (satisfies_fmla_append (hChunk14) (hChunk15))))) (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (hChunk16) (hChunk17)) (satisfies_fmla_append (hChunk18) (hChunk19))) (satisfies_fmla_append (satisfies_fmla_append (hChunk20) (hChunk21)) (satisfies_fmla_append (hChunk22) (hChunk23)))) (satisfies_fmla_append (satisfies_fmla_append (satisfies_fmla_append (hChunk24) (hChunk25)) (satisfies_fmla_append (hChunk26) (hChunk27))) (satisfies_fmla_append (satisfies_fmla_append (hChunk28) (hChunk29)) (satisfies_fmla_append (hChunk30) (hChunk31)))))
  exact TuzaRankFour.Certificates.Segmented.Order12Skeleton03.refutation v hFormula

end TuzaRankFour.Certificates.Semantic.Order12Skeleton03
