import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton00

certificate_locked {
semantic_marked_packing_binary markedPacking 9 0
  "../../../Certificates/semantic-cuts/order09-skeleton00.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton00.cnf")

semantic_cut_slices_binary cutChunk 9 0 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton00.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order09Skeleton00
