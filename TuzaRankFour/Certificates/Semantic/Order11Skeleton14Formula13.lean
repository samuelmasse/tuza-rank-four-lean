import TuzaRankFour.Certificates.Semantic.Order11Skeleton14Formula12

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton14

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

certificate_locked {
theorem cutChunk26_valid : cutsValidBool 11 cutChunk26 = true := by
  decide

theorem formulaChunk26_eq :
    formulaChunk26 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk26 := by
  decide

theorem cutChunk27_valid : cutsValidBool 11 cutChunk27 = true := by
  decide

theorem formulaChunk27_eq :
    formulaChunk27 =
      ((baseFormula 11 markedPacking).drop 730).take 0 ++
        cutFormula 11 cutChunk27 := by
  decide

}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton14
