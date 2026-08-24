import TuzaRankFour.Certificates.Semantic.Order09Skeleton02Data

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton02

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

theorem cutChunk0_valid : cutsValidBool 9 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 9 markedPacking).drop 0).take 385 ++
        cutFormula 9 cutChunk0 := by
  decide

theorem cutChunk1_valid : cutsValidBool 9 cutChunk1 = true := by
  decide

theorem formulaChunk1_eq :
    formulaChunk1 =
      ((baseFormula 9 markedPacking).drop 385).take 0 ++
        cutFormula 9 cutChunk1 := by
  decide

theorem cutChunk2_valid : cutsValidBool 9 cutChunk2 = true := by
  decide

theorem formulaChunk2_eq :
    formulaChunk2 =
      ((baseFormula 9 markedPacking).drop 385).take 0 ++
        cutFormula 9 cutChunk2 := by
  decide

theorem cutChunk3_valid : cutsValidBool 9 cutChunk3 = true := by
  decide

theorem formulaChunk3_eq :
    formulaChunk3 =
      ((baseFormula 9 markedPacking).drop 385).take 0 ++
        cutFormula 9 cutChunk3 := by
  decide

end TuzaRankFour.Certificates.Semantic.Order09Skeleton02
