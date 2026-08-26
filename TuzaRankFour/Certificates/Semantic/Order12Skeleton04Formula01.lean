import TuzaRankFour.Certificates.Semantic.Order12Skeleton04Formula00

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton04

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk2_valid : cutsValidBool 12 cutChunk2 = true := by
  decide

theorem formulaChunk2_eq :
    formulaChunk2 =
      ((baseFormula 12 markedPacking).drop 587).take 293 ++
        cutFormula 12 cutChunk2 := by
  decide

theorem cutChunk3_valid : cutsValidBool 12 cutChunk3 = true := by
  decide

theorem formulaChunk3_eq :
    formulaChunk3 =
      ((baseFormula 12 markedPacking).drop 880).take 82 ++
        cutFormula 12 cutChunk3 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton04
