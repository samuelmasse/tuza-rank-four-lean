import TuzaRankFour.Certificates.Semantic.Order12Skeleton01Formula06

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton01

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk14_valid : cutsValidBool 12 cutChunk14 = true := by
  decide

theorem formulaChunk14_eq :
    formulaChunk14 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk14 := by
  decide

theorem cutChunk15_valid : cutsValidBool 12 cutChunk15 = true := by
  decide

theorem formulaChunk15_eq :
    formulaChunk15 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk15 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton01
