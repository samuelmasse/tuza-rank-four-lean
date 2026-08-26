import TuzaRankFour.Certificates.Semantic.Order10Skeleton10Formula02

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton10

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk6_valid : cutsValidBool 10 cutChunk6 = true := by
  decide

theorem formulaChunk6_eq :
    formulaChunk6 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk6 := by
  decide

theorem cutChunk7_valid : cutsValidBool 10 cutChunk7 = true := by
  decide

theorem formulaChunk7_eq :
    formulaChunk7 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk7 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton10
