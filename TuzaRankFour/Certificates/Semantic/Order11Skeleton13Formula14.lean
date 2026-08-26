import TuzaRankFour.Certificates.Semantic.Order11Skeleton13Formula13

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk28_valid : cutsValidBool 11 cutChunk28 = true := by
  decide

theorem formulaChunk28_eq :
    formulaChunk28 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk28 := by
  decide

theorem cutChunk29_valid : cutsValidBool 11 cutChunk29 = true := by
  decide

theorem formulaChunk29_eq :
    formulaChunk29 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk29 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton13
