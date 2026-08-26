import TuzaRankFour.Certificates.Semantic.Order12Skeleton08Formula14

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton08

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk30_valid : cutsValidBool 12 cutChunk30 = true := by
  decide

theorem formulaChunk30_eq :
    formulaChunk30 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk30 := by
  decide

theorem cutChunk31_valid : cutsValidBool 12 cutChunk31 = true := by
  decide

theorem formulaChunk31_eq :
    formulaChunk31 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk31 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton08
