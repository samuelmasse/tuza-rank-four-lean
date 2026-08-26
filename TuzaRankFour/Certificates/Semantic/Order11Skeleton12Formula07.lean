import TuzaRankFour.Certificates.Semantic.Order11Skeleton12Formula06

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton12

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk14_valid : cutsValidBool 11 cutChunk14 = true := by
  decide

theorem formulaChunk14_eq :
    formulaChunk14 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk14 := by
  decide

theorem cutChunk15_valid : cutsValidBool 11 cutChunk15 = true := by
  decide

theorem formulaChunk15_eq :
    formulaChunk15 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk15 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton12
