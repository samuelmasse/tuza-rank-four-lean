import TuzaRankFour.Certificates.Semantic.Order12Skeleton15Formula23

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton15

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk48_valid : cutsValidBool 12 cutChunk48 = true := by
  decide

theorem formulaChunk48_eq :
    formulaChunk48 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk48 := by
  decide

theorem cutChunk49_valid : cutsValidBool 12 cutChunk49 = true := by
  decide

theorem formulaChunk49_eq :
    formulaChunk49 =
      ((baseFormula 12 markedPacking).drop 962).take 0 ++
        cutFormula 12 cutChunk49 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton15
