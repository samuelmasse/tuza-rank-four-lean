import TuzaRankFour.PackingClassificationShard00
import TuzaRankFour.PackingClassificationShard01
import TuzaRankFour.PackingClassificationShard02
import TuzaRankFour.PackingClassificationShard03
import TuzaRankFour.PackingClassificationShard04
import TuzaRankFour.PackingClassificationShard05
import TuzaRankFour.PackingClassificationShard06
import TuzaRankFour.PackingClassificationShard07

/-!
# Complete four-packing classification

This module joins the eight kernel-reduced finite shards into the exact
sixteen-type classification used by the rank-four endpoint.
-/

namespace TuzaRankFour.PackingClassification

/-- Every valid shared-incidence family of four edge-disjoint triangles is,
up to a permutation of the four triangles, one of the sixteen frozen
canonical families. -/
theorem classifySharedFamilies (F : SharedFamily) (hValid : validBool F = true) :
    ∃ s : Fin 16, ∃ p : Equiv.Perm Block,
      permuteFamily p F = canonicalSharedFamily s := by
  have hPowerset : F ∈ sharedMasks.powerset := by
    rw [Finset.mem_powerset]
    intro m hm
    simp only [sharedMasks, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (validBool_eq_true_iff F).mp hValid |>.1 m hm
  obtain ⟨k, hk⟩ := mem_candidateShard F hPowerset
  fin_cases k
  · exact classifyCandidateShard00 ⟨F, hk⟩ hValid
  · exact classifyCandidateShard01 ⟨F, hk⟩ hValid
  · exact classifyCandidateShard02 ⟨F, hk⟩ hValid
  · exact classifyCandidateShard03 ⟨F, hk⟩ hValid
  · exact classifyCandidateShard04 ⟨F, hk⟩ hValid
  · exact classifyCandidateShard05 ⟨F, hk⟩ hValid
  · exact classifyCandidateShard06 ⟨F, hk⟩ hValid
  · exact classifyCandidateShard07 ⟨F, hk⟩ hValid

end TuzaRankFour.PackingClassification
