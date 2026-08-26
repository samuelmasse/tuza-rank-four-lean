import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton13

certificate_locked {
semantic_marked_packing_binary markedPacking 10 13
  "../../../Certificates/semantic-cuts/order10-skeleton13.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton13.cnf")

semantic_cut_slices_binary cutChunk 10 13 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton13.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton13
