import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula29

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk60_valid : cutsValidBool 12 cutChunk60 = true := by
  decide

theorem formulaChunk60_eq :
    formulaChunk60 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk60 := by
  decide

theorem cutChunk61_valid : cutsValidBool 12 cutChunk61 = true := by
  decide

theorem formulaChunk61_eq :
    formulaChunk61 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk61 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
