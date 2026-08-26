import TuzaRankFour.Certificates.Semantic.Order11Skeleton07Formula01

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton07

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk4_valid : cutsValidBool 11 cutChunk4 = true := by
  decide

theorem formulaChunk4_eq :
    formulaChunk4 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk4 := by
  decide

theorem cutChunk5_valid : cutsValidBool 11 cutChunk5 = true := by
  decide

theorem formulaChunk5_eq :
    formulaChunk5 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk5 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton07
