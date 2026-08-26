import TuzaRankFour.Certificates.Semantic.Order11Skeleton13Formula08

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton13

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk18_valid : cutsValidBool 11 cutChunk18 = true := by
  decide

theorem formulaChunk18_eq :
    formulaChunk18 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk18 := by
  decide

theorem cutChunk19_valid : cutsValidBool 11 cutChunk19 = true := by
  decide

theorem formulaChunk19_eq :
    formulaChunk19 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk19 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton13
