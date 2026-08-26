import TuzaRankFour.Certificates.Semantic.Order12Skeleton04Formula08

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton04

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk18_valid : cutsValidBool 12 cutChunk18 = true := by
  decide

theorem formulaChunk18_eq :
    formulaChunk18 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk18 := by
  decide

theorem cutChunk19_valid : cutsValidBool 12 cutChunk19 = true := by
  decide

theorem formulaChunk19_eq :
    formulaChunk19 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk19 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton04
