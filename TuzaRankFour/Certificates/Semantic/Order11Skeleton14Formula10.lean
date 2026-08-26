import TuzaRankFour.Certificates.Semantic.Order11Skeleton14Formula09

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton14

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk20_valid : cutsValidBool 11 cutChunk20 = true := by
  decide

theorem formulaChunk20_eq :
    formulaChunk20 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk20 := by
  decide

theorem cutChunk21_valid : cutsValidBool 11 cutChunk21 = true := by
  decide

theorem formulaChunk21_eq :
    formulaChunk21 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk21 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton14
