import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula18

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk38_valid : cutsValidBool 12 cutChunk38 = true := by
  decide

theorem formulaChunk38_eq :
    formulaChunk38 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk38 := by
  decide

theorem cutChunk39_valid : cutsValidBool 12 cutChunk39 = true := by
  decide

theorem formulaChunk39_eq :
    formulaChunk39 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk39 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
