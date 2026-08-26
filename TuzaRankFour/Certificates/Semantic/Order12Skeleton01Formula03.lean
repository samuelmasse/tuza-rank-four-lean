import TuzaRankFour.Certificates.Semantic.Order12Skeleton01Formula02

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton01

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk6_valid : cutsValidBool 12 cutChunk6 = true := by
  decide

theorem formulaChunk6_eq :
    formulaChunk6 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk6 := by
  decide

theorem cutChunk7_valid : cutsValidBool 12 cutChunk7 = true := by
  decide

theorem formulaChunk7_eq :
    formulaChunk7 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk7 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton01
