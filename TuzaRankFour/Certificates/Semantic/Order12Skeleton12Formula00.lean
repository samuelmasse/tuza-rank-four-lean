import TuzaRankFour.Certificates.Semantic.Order12Skeleton12Data

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton12

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
      ((baseFormula 12 markedPacking).drop 0).take 287 ++
        cutFormula 12 cutChunk0 := by
  decide

theorem cutChunk1_valid : cutsValidBool 12 cutChunk1 = true := by
  decide

theorem formulaChunk1_eq :
    formulaChunk1 =
      ((baseFormula 12 markedPacking).drop 287).take 287 ++
        cutFormula 12 cutChunk1 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton12
