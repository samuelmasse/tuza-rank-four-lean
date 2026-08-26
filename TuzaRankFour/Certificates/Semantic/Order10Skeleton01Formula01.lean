import TuzaRankFour.Certificates.Semantic.Order10Skeleton01Formula00

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton01

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk2_valid : cutsValidBool 10 cutChunk2 = true := by
  decide

theorem formulaChunk2_eq :
    formulaChunk2 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk2 := by
  decide

theorem cutChunk3_valid : cutsValidBool 10 cutChunk3 = true := by
  decide

theorem formulaChunk3_eq :
    formulaChunk3 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk3 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton01
