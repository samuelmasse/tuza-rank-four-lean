import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula19

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk40_valid : cutsValidBool 12 cutChunk40 = true := by
  decide

theorem formulaChunk40_eq :
    formulaChunk40 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk40 := by
  decide

theorem cutChunk41_valid : cutsValidBool 12 cutChunk41 = true := by
  decide

theorem formulaChunk41_eq :
    formulaChunk41 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk41 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
