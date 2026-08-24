import TuzaRankFour.PackingClassification

namespace TuzaRankFour.PackingClassification

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Kernel-reduced classification shard 2 of 7. -/
theorem classifyCandidateShard02 :
    ∀ F : {F : SharedFamily // F ∈ candidateShard 2},
      validBool F.val = true →
      ∃ s : Fin 16, ∃ p : Equiv.Perm Block,
        permuteFamily p F.val = canonicalSharedFamily s := by
  decide

end TuzaRankFour.PackingClassification
