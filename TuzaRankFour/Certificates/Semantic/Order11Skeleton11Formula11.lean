import TuzaRankFour.Certificates.Semantic.Order11Skeleton11Formula10

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton11

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk22_valid : cutsValidBool 11 cutChunk22 = true := by
  decide

theorem formulaChunk22_eq :
    formulaChunk22 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk22 := by
  decide

theorem cutChunk23_valid : cutsValidBool 11 cutChunk23 = true := by
  decide

theorem formulaChunk23_eq :
    formulaChunk23 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk23 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton11
