import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton12

certificate_locked {
semantic_marked_packing_binary markedPacking 10 12
  "../../../Certificates/semantic-cuts/order10-skeleton12.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton12.cnf")

semantic_cut_slices_binary cutChunk 10 12 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton12.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton12
