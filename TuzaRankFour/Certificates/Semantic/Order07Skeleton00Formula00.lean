import TuzaRankFour.Certificates.Semantic.Order07Skeleton00Data

namespace TuzaRankFour.Certificates.Semantic.Order07Skeleton00

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

certificate_locked {
theorem cutChunk0_valid : cutsValidBool 7 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 7 markedPacking).drop 0).take 172 ++
        cutFormula 7 cutChunk0 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order07Skeleton00
