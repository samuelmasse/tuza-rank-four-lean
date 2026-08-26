import TuzaRankFour.Certificates.Semantic.Order11Skeleton03Formula03

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton03

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk8_valid : cutsValidBool 11 cutChunk8 = true := by
  decide

theorem formulaChunk8_eq :
    formulaChunk8 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk8 := by
  decide

theorem cutChunk9_valid : cutsValidBool 11 cutChunk9 = true := by
  decide

theorem formulaChunk9_eq :
    formulaChunk9 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk9 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton03
