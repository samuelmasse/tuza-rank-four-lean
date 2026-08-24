import TuzaRankFour.Certificates.Semantic.Order12Skeleton03Formula00

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton03

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cutChunk8_valid : cutsValidBool 12 cutChunk8 = true := by
  decide

theorem formulaChunk8_eq :
    formulaChunk8 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk8 := by
  decide

theorem cutChunk9_valid : cutsValidBool 12 cutChunk9 = true := by
  decide

theorem formulaChunk9_eq :
    formulaChunk9 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk9 := by
  decide

theorem cutChunk10_valid : cutsValidBool 12 cutChunk10 = true := by
  decide

theorem formulaChunk10_eq :
    formulaChunk10 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk10 := by
  decide

theorem cutChunk11_valid : cutsValidBool 12 cutChunk11 = true := by
  decide

theorem formulaChunk11_eq :
    formulaChunk11 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk11 := by
  decide

theorem cutChunk12_valid : cutsValidBool 12 cutChunk12 = true := by
  decide

theorem formulaChunk12_eq :
    formulaChunk12 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk12 := by
  decide

theorem cutChunk13_valid : cutsValidBool 12 cutChunk13 = true := by
  decide

theorem formulaChunk13_eq :
    formulaChunk13 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk13 := by
  decide

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

end TuzaRankFour.Certificates.Semantic.Order12Skeleton03
