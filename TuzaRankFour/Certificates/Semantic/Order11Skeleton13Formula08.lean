import TuzaRankFour.Certificates.Semantic.Order11Skeleton13Formula07

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk16_valid : cutsValidBool 11 cutChunk16 = true := by
  decide

theorem formulaChunk16_eq :
    formulaChunk16 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk16 := by
  decide

theorem cutChunk17_valid : cutsValidBool 11 cutChunk17 = true := by
  decide

theorem formulaChunk17_eq :
    formulaChunk17 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk17 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton13
