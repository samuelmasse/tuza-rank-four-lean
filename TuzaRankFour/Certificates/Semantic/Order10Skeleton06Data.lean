import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton06

certificate_locked {
semantic_marked_packing_binary markedPacking 10 6
  "../../../Certificates/semantic-cuts/order10-skeleton06.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton06.cnf")

semantic_cut_slices_binary cutChunk 10 6 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton06.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton06
