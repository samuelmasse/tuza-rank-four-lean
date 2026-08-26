import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula28

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk58_valid : cutsValidBool 12 cutChunk58 = true := by
  decide

theorem formulaChunk58_eq :
    formulaChunk58 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk58 := by
  decide

theorem cutChunk59_valid : cutsValidBool 12 cutChunk59 = true := by
  decide

theorem formulaChunk59_eq :
    formulaChunk59 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk59 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
