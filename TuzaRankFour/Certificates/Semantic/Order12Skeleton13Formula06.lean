import TuzaRankFour.Certificates.Semantic.Order12Skeleton13Formula05

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk12_valid : cutsValidBool 12 cutChunk12 = true := by
  decide

theorem formulaChunk12_eq :
    formulaChunk12 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk12 := by
  decide

theorem cutChunk13_valid : cutsValidBool 12 cutChunk13 = true := by
  decide

theorem formulaChunk13_eq :
    formulaChunk13 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk13 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton13
