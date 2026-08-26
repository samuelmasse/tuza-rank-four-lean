import TuzaRankFour.Certificates.Semantic.Order12Skeleton13Formula13

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk28_valid : cutsValidBool 12 cutChunk28 = true := by
  decide

theorem formulaChunk28_eq :
    formulaChunk28 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk28 := by
  decide

theorem cutChunk29_valid : cutsValidBool 12 cutChunk29 = true := by
  decide

theorem formulaChunk29_eq :
    formulaChunk29 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk29 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton13
