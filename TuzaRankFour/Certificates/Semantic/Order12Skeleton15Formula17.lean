import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula16

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk34_valid : cutsValidBool 12 cutChunk34 = true := by
  decide

theorem formulaChunk34_eq :
    formulaChunk34 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk34 := by
  decide

theorem cutChunk35_valid : cutsValidBool 12 cutChunk35 = true := by
  decide

theorem formulaChunk35_eq :
    formulaChunk35 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk35 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
