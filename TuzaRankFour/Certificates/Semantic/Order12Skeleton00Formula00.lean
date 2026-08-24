import TuzaRankFour.Certificates.Semantic.Order12Skeleton00Data

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton00

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

deriving instance DecidableEq for Sat.Literal
deriving instance DecidableEq for Sat.Clause

theorem cutChunk0_valid : cutsValidBool 12 cutChunk0 = true := by
  decide

theorem formulaChunk0_eq :
    formulaChunk0 =
      ((baseFormula 12 markedPacking).drop 0).take 424 ++
        cutFormula 12 cutChunk0 := by
  decide

theorem cutChunk1_valid : cutsValidBool 12 cutChunk1 = true := by
  decide

theorem formulaChunk1_eq :
    formulaChunk1 =
      ((baseFormula 12 markedPacking).drop 424).take 425 ++
        cutFormula 12 cutChunk1 := by
  decide

theorem cutChunk2_valid : cutsValidBool 12 cutChunk2 = true := by
  decide

theorem formulaChunk2_eq :
    formulaChunk2 =
      ((baseFormula 12 markedPacking).drop 849).take 113 ++
        cutFormula 12 cutChunk2 := by
  decide

theorem cutChunk3_valid : cutsValidBool 12 cutChunk3 = true := by
  decide

theorem formulaChunk3_eq :
    formulaChunk3 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk3 := by
  decide

theorem cutChunk4_valid : cutsValidBool 12 cutChunk4 = true := by
  decide

theorem formulaChunk4_eq :
    formulaChunk4 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk4 := by
  decide

theorem cutChunk5_valid : cutsValidBool 12 cutChunk5 = true := by
  decide

theorem formulaChunk5_eq :
    formulaChunk5 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk5 := by
  decide

theorem cutChunk6_valid : cutsValidBool 12 cutChunk6 = true := by
  decide

theorem formulaChunk6_eq :
    formulaChunk6 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk6 := by
  decide

theorem cutChunk7_valid : cutsValidBool 12 cutChunk7 = true := by
  decide

theorem formulaChunk7_eq :
    formulaChunk7 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk7 := by
  decide

end TuzaRankFour.Certificates.Semantic.Order12Skeleton00
