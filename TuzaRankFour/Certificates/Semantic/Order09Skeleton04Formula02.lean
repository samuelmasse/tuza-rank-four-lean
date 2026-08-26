import TuzaRankFour.Certificates.Semantic.Order09Skeleton04Formula01

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton04

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk4_valid : cutsValidBool 9 cutChunk4 = true := by
  decide

theorem formulaChunk4_eq :
    formulaChunk4 =
      ((baseFormula 9 markedPacking).drop 385).take 0 ++
        cutFormula 9 cutChunk4 := by
  decide

theorem cutChunk5_valid : cutsValidBool 9 cutChunk5 = true := by
  decide

theorem formulaChunk5_eq :
    formulaChunk5 =
      ((baseFormula 9 markedPacking).drop 385).take 0 ++
        cutFormula 9 cutChunk5 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order09Skeleton04
