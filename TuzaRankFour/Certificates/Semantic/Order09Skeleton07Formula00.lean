import TuzaRankFour.Certificates.Semantic.Order09Skeleton07Data

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton07

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

certificate_locked {
theorem cutChunk0_valid : cutsValidBool 9 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 9 markedPacking).drop 0).take 308 ++
        cutFormula 9 cutChunk0 := by
  decide

theorem cutChunk1_valid : cutsValidBool 9 cutChunk1 = true := by
  decide

theorem formulaChunk1_eq :
    formulaChunk1 =
      ((baseFormula 9 markedPacking).drop 308).take 77 ++
        cutFormula 9 cutChunk1 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order09Skeleton07
