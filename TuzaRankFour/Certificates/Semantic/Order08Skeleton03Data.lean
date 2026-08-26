import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order08Skeleton03

certificate_locked {
semantic_marked_packing_binary markedPacking 8 3
  "../../../Certificates/semantic-cuts/order08-skeleton03.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order08-skeleton03.cnf")

semantic_cut_slices_binary cutChunk 8 3 264 512
  "../../../Certificates/semantic-cuts/order08-skeleton03.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order08Skeleton03
