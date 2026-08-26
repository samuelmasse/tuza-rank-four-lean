import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton03

certificate_locked {
semantic_marked_packing_binary markedPacking 10 3
  "../../../Certificates/semantic-cuts/order10-skeleton03.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton03.cnf")

semantic_cut_slices_binary cutChunk 10 3 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton03.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton03
