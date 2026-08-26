import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula17

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk36_valid : cutsValidBool 12 cutChunk36 = true := by
  decide

theorem formulaChunk36_eq :
    formulaChunk36 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk36 := by
  decide

theorem cutChunk37_valid : cutsValidBool 12 cutChunk37 = true := by
  decide

theorem formulaChunk37_eq :
    formulaChunk37 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk37 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
