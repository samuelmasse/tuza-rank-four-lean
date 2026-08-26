import TuzaRankFour.Certificates.Semantic.Order12Skeleton13Formula00

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk2_valid : cutsValidBool 12 cutChunk2 = true := by
  decide

theorem formulaChunk2_eq :
    formulaChunk2 =
      ((baseFormula 12 markedPacking).drop 835).take 127 ++
        cutFormula 12 cutChunk2 := by
  decide

theorem cutChunk3_valid : cutsValidBool 12 cutChunk3 = true := by
  decide

theorem formulaChunk3_eq :
    formulaChunk3 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk3 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton13
