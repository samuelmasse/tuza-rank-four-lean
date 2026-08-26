import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula15

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk32_valid : cutsValidBool 12 cutChunk32 = true := by
  decide

theorem formulaChunk32_eq :
    formulaChunk32 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk32 := by
  decide

theorem cutChunk33_valid : cutsValidBool 12 cutChunk33 = true := by
  decide

theorem formulaChunk33_eq :
    formulaChunk33 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk33 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
