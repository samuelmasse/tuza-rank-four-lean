import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula24

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk50_valid : cutsValidBool 12 cutChunk50 = true := by
  decide

theorem formulaChunk50_eq :
    formulaChunk50 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk50 := by
  decide

theorem cutChunk51_valid : cutsValidBool 12 cutChunk51 = true := by
  decide

theorem formulaChunk51_eq :
    formulaChunk51 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk51 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
