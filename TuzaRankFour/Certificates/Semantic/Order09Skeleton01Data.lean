import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton01

certificate_locked {
semantic_marked_packing_binary markedPacking 9 1
  "../../../Certificates/semantic-cuts/order09-skeleton01.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton01.cnf")

semantic_cut_slices_binary cutChunk 9 1 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton01.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order09Skeleton01
