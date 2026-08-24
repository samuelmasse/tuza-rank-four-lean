import TuzaRankFour.Certificates.Semantic.Order06Skeleton00Data

namespace TuzaRankFour.Certificates.Semantic.Order06Skeleton00

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

theorem cutChunk0_valid : cutsValidBool 6 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 6 markedPacking).drop 0).take 105 ++
        cutFormula 6 cutChunk0 := by
  decide

end TuzaRankFour.Certificates.Semantic.Order06Skeleton00
