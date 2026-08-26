import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula27

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk56_valid : cutsValidBool 12 cutChunk56 = true := by
  decide

theorem formulaChunk56_eq :
    formulaChunk56 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk56 := by
  decide

theorem cutChunk57_valid : cutsValidBool 12 cutChunk57 = true := by
  decide

theorem formulaChunk57_eq :
    formulaChunk57 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk57 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
