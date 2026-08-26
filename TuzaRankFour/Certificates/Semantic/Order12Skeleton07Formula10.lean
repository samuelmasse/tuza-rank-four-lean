import TuzaRankFour.Certificates.Semantic.Order12Skeleton07Formula09

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton07

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk20_valid : cutsValidBool 12 cutChunk20 = true := by
  decide

theorem formulaChunk20_eq :
    formulaChunk20 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk20 := by
  decide

theorem cutChunk21_valid : cutsValidBool 12 cutChunk21 = true := by
  decide

theorem formulaChunk21_eq :
    formulaChunk21 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk21 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton07
