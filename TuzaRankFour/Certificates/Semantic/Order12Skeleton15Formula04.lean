import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula03

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cutChunk32_valid : cutsValidBool 12 cutChunk32 = true := by
  decide

theorem formulaChunk32_eq :
    formulaChunk32 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk32 := by
  decide

theorem cutChunk33_valid : cutsValidBool 12 cutChunk33 = true := by
  decide

theorem formulaChunk33_eq :
    formulaChunk33 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk33 := by
  decide

theorem cutChunk34_valid : cutsValidBool 12 cutChunk34 = true := by
  decide

theorem formulaChunk34_eq :
    formulaChunk34 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk34 := by
  decide

theorem cutChunk35_valid : cutsValidBool 12 cutChunk35 = true := by
  decide

theorem formulaChunk35_eq :
    formulaChunk35 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk35 := by
  decide

theorem cutChunk36_valid : cutsValidBool 12 cutChunk36 = true := by
  decide

theorem formulaChunk36_eq :
    formulaChunk36 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk36 := by
  decide

theorem cutChunk37_valid : cutsValidBool 12 cutChunk37 = true := by
  decide

theorem formulaChunk37_eq :
    formulaChunk37 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk37 := by
  decide

theorem cutChunk38_valid : cutsValidBool 12 cutChunk38 = true := by
  decide

theorem formulaChunk38_eq :
    formulaChunk38 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk38 := by
  decide

theorem cutChunk39_valid : cutsValidBool 12 cutChunk39 = true := by
  decide

theorem formulaChunk39_eq :
    formulaChunk39 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk39 := by
  decide

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
