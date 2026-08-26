import TuzaRankFour.Certificates.Semantic.Order12Skeleton14Data

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton14

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

certificate_locked {
theorem cutChunk0_valid : cutsValidBool 12 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 12 markedPacking).drop 0).take 451 ++
        cutFormula 12 cutChunk0 := by
  decide

theorem cutChunk1_valid : cutsValidBool 12 cutChunk1 = true := by
  decide

theorem formulaChunk1_eq :
    formulaChunk1 =
      ((baseFormula 12 markedPacking).drop 451).take 452 ++
        cutFormula 12 cutChunk1 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton14
