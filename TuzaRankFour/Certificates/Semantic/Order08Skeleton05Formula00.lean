import TuzaRankFour.Certificates.Semantic.Order08Skeleton05Data

namespace TuzaRankFour.Certificates.Semantic.Order08Skeleton05

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

certificate_locked {
theorem cutChunk0_valid : cutsValidBool 8 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 8 markedPacking).drop 0).take 264 ++
        cutFormula 8 cutChunk0 := by
  decide

theorem cutChunk1_valid : cutsValidBool 8 cutChunk1 = true := by
  decide

theorem formulaChunk1_eq :
    formulaChunk1 =
      ((baseFormula 8 markedPacking).drop 264).take 0 ++
        cutFormula 8 cutChunk1 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order08Skeleton05
