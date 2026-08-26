import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton09

certificate_locked {
semantic_marked_packing_binary markedPacking 9 9
  "../../../Certificates/semantic-cuts/order09-skeleton09.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton09.cnf")

semantic_cut_slices_binary cutChunk 9 9 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton09.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order09Skeleton09
