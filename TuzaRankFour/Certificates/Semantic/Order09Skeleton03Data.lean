import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton03

certificate_locked {
semantic_marked_packing_binary markedPacking 9 3
  "../../../Certificates/semantic-cuts/order09-skeleton03.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton03.cnf")

semantic_cut_slices_binary cutChunk 9 3 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton03.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order09Skeleton03
