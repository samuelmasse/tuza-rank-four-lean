import TuzaRankFour.Certificates.Semantic.Order11Skeleton04Formula02

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton04

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk6_valid : cutsValidBool 11 cutChunk6 = true := by
  decide

theorem formulaChunk6_eq :
    formulaChunk6 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk6 := by
  decide

theorem cutChunk7_valid : cutsValidBool 11 cutChunk7 = true := by
  decide

theorem formulaChunk7_eq :
    formulaChunk7 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk7 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton04
