import TuzaRankFour.Certificates.Semantic.Order11Skeleton08Data

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton08

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

certificate_locked {
theorem cutChunk0_valid : cutsValidBool 11 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 11 markedPacking).drop 0).take 392 ++
        cutFormula 11 cutChunk0 := by
  decide

theorem cutChunk1_valid : cutsValidBool 11 cutChunk1 = true := by
  decide

theorem formulaChunk1_eq :
    formulaChunk1 =
      ((baseFormula 11 markedPacking).drop 392).take 338 ++
        cutFormula 11 cutChunk1 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton08
