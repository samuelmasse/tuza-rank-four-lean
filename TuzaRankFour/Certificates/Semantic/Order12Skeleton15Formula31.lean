import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula30

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk62_valid : cutsValidBool 12 cutChunk62 = true := by
  decide

theorem formulaChunk62_eq :
    formulaChunk62 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk62 := by
  decide

theorem cutChunk63_valid : cutsValidBool 12 cutChunk63 = true := by
  decide

theorem formulaChunk63_eq :
    formulaChunk63 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk63 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
