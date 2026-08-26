import TuzaRankFour.Certificates.Semantic.Order11Skeleton02Formula04

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton02

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk10_valid : cutsValidBool 11 cutChunk10 = true := by
  decide

theorem formulaChunk10_eq :
    formulaChunk10 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk10 := by
  decide

theorem cutChunk11_valid : cutsValidBool 11 cutChunk11 = true := by
  decide

theorem formulaChunk11_eq :
    formulaChunk11 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk11 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton02
