import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula21

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk44_valid : cutsValidBool 12 cutChunk44 = true := by
  decide

theorem formulaChunk44_eq :
    formulaChunk44 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk44 := by
  decide

theorem cutChunk45_valid : cutsValidBool 12 cutChunk45 = true := by
  decide

theorem formulaChunk45_eq :
    formulaChunk45 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk45 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
