import TuzaRankFour.Certificates.Semantic.Order12Skeleton10Formula07

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton10

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk16_valid : cutsValidBool 12 cutChunk16 = true := by
  decide

theorem formulaChunk16_eq :
    formulaChunk16 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk16 := by
  decide

theorem cutChunk17_valid : cutsValidBool 12 cutChunk17 = true := by
  decide

theorem formulaChunk17_eq :
    formulaChunk17 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk17 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton10
