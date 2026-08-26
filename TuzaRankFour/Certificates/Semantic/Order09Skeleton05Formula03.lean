import TuzaRankFour.Certificates.Semantic.Order09Skeleton05Formula02

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton05

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk6_valid : cutsValidBool 9 cutChunk6 = true := by
  decide

theorem formulaChunk6_eq :
    formulaChunk6 =
      ((baseFormula 9 markedPacking).drop 385).take 0 ++
        cutFormula 9 cutChunk6 := by
  decide

theorem cutChunk7_valid : cutsValidBool 9 cutChunk7 = true := by
  decide

theorem formulaChunk7_eq :
    formulaChunk7 =
      ((baseFormula 9 markedPacking).drop 385).take 0 ++
        cutFormula 9 cutChunk7 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order09Skeleton05
