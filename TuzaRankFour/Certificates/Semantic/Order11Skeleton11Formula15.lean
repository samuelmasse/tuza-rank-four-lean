import TuzaRankFour.Certificates.Semantic.Order11Skeleton11Formula14

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton11

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk30_valid : cutsValidBool 11 cutChunk30 = true := by
  decide

theorem formulaChunk30_eq :
    formulaChunk30 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk30 := by
  decide

theorem cutChunk31_valid : cutsValidBool 11 cutChunk31 = true := by
  decide

theorem formulaChunk31_eq :
    formulaChunk31 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk31 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton11
