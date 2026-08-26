import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula25

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk52_valid : cutsValidBool 12 cutChunk52 = true := by
  decide

theorem formulaChunk52_eq :
    formulaChunk52 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk52 := by
  decide

theorem cutChunk53_valid : cutsValidBool 12 cutChunk53 = true := by
  decide

theorem formulaChunk53_eq :
    formulaChunk53 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk53 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
