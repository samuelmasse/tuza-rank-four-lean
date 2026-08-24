import TuzaRankFour.Certificates.Semantic.Order12Skeleton05Formula01

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton05

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cutChunk16_valid : cutsValidBool 12 cutChunk16 = true := by
  decide

theorem formulaChunk16_eq :
    formulaChunk16 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk16 := by
  decide

theorem cutChunk17_valid : cutsValidBool 12 cutChunk17 = true := by
  decide

theorem formulaChunk17_eq :
    formulaChunk17 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk17 := by
  decide

theorem cutChunk18_valid : cutsValidBool 12 cutChunk18 = true := by
  decide

theorem formulaChunk18_eq :
    formulaChunk18 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk18 := by
  decide

theorem cutChunk19_valid : cutsValidBool 12 cutChunk19 = true := by
  decide

theorem formulaChunk19_eq :
    formulaChunk19 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk19 := by
  decide

theorem cutChunk20_valid : cutsValidBool 12 cutChunk20 = true := by
  decide

theorem formulaChunk20_eq :
    formulaChunk20 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk20 := by
  decide

theorem cutChunk21_valid : cutsValidBool 12 cutChunk21 = true := by
  decide

theorem formulaChunk21_eq :
    formulaChunk21 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk21 := by
  decide

theorem cutChunk22_valid : cutsValidBool 12 cutChunk22 = true := by
  decide

theorem formulaChunk22_eq :
    formulaChunk22 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk22 := by
  decide

theorem cutChunk23_valid : cutsValidBool 12 cutChunk23 = true := by
  decide

theorem formulaChunk23_eq :
    formulaChunk23 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk23 := by
  decide

end TuzaRankFour.Certificates.Semantic.Order12Skeleton05
