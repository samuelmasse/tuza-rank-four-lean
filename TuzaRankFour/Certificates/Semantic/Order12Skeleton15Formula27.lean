import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula26

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk54_valid : cutsValidBool 12 cutChunk54 = true := by
  decide

theorem formulaChunk54_eq :
    formulaChunk54 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk54 := by
  decide

theorem cutChunk55_valid : cutsValidBool 12 cutChunk55 = true := by
  decide

theorem formulaChunk55_eq :
    formulaChunk55 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk55 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
