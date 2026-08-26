import TuzaRankFour.Certificates.Semantic.Order12Skeleton13Formula11

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk24_valid : cutsValidBool 12 cutChunk24 = true := by
  decide

theorem formulaChunk24_eq :
    formulaChunk24 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk24 := by
  decide

theorem cutChunk25_valid : cutsValidBool 12 cutChunk25 = true := by
  decide

theorem formulaChunk25_eq :
    formulaChunk25 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk25 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton13
