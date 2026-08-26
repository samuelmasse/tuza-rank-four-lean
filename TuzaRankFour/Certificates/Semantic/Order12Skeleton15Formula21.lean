import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula20

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk42_valid : cutsValidBool 12 cutChunk42 = true := by
  decide

theorem formulaChunk42_eq :
    formulaChunk42 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk42 := by
  decide

theorem cutChunk43_valid : cutsValidBool 12 cutChunk43 = true := by
  decide

theorem formulaChunk43_eq :
    formulaChunk43 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk43 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
