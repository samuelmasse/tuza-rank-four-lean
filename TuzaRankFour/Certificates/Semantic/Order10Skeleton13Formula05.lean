import TuzaRankFour.Certificates.Semantic.Order10Skeleton13Formula04

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk10_valid : cutsValidBool 10 cutChunk10 = true := by
  decide

theorem formulaChunk10_eq :
    formulaChunk10 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk10 := by
  decide

theorem cutChunk11_valid : cutsValidBool 10 cutChunk11 = true := by
  decide

theorem formulaChunk11_eq :
    formulaChunk11 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk11 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton13
