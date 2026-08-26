import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula22

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk46_valid : cutsValidBool 12 cutChunk46 = true := by
  decide

theorem formulaChunk46_eq :
    formulaChunk46 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk46 := by
  decide

theorem cutChunk47_valid : cutsValidBool 12 cutChunk47 = true := by
  decide

theorem formulaChunk47_eq :
    formulaChunk47 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk47 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
