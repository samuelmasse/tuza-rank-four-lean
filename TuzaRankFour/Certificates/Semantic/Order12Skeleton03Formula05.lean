import TuzaRankFour.Certificates.Semantic.Order12Skeleton03Formula04

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton03

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk10_valid : cutsValidBool 12 cutChunk10 = true := by
  decide

theorem formulaChunk10_eq :
    formulaChunk10 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk10 := by
  decide

theorem cutChunk11_valid : cutsValidBool 12 cutChunk11 = true := by
  decide

theorem formulaChunk11_eq :
    formulaChunk11 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk11 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton03
