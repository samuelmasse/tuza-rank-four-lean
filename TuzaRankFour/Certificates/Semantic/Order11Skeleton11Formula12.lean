import TuzaRankFour.Certificates.Semantic.Order11Skeleton11Formula11

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton11

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk24_valid : cutsValidBool 11 cutChunk24 = true := by
  decide

theorem formulaChunk24_eq :
    formulaChunk24 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk24 := by
  decide

theorem cutChunk25_valid : cutsValidBool 11 cutChunk25 = true := by
  decide

theorem formulaChunk25_eq :
    formulaChunk25 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk25 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton11
