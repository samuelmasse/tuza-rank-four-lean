import TuzaRankFour.Certificates.Semantic.Order10Skeleton06Formula03

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton06

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk8_valid : cutsValidBool 10 cutChunk8 = true := by
  decide

theorem formulaChunk8_eq :
    formulaChunk8 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk8 := by
  decide

theorem cutChunk9_valid : cutsValidBool 10 cutChunk9 = true := by
  decide

theorem formulaChunk9_eq :
    formulaChunk9 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk9 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton06
