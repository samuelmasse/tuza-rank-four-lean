import TuzaRankFour.Certificates.Semantic.Order10Skeleton10Formula01

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton10

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk4_valid : cutsValidBool 10 cutChunk4 = true := by
  decide

theorem formulaChunk4_eq :
    formulaChunk4 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk4 := by
  decide

theorem cutChunk5_valid : cutsValidBool 10 cutChunk5 = true := by
  decide

theorem formulaChunk5_eq :
    formulaChunk5 =
      ((baseFormula 10 markedPacking).drop 539).take 0 ++
        cutFormula 10 cutChunk5 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton10
