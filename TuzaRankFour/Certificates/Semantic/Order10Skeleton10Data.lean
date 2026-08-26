import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton10

certificate_locked {
semantic_marked_packing_binary markedPacking 10 10
  "../../../Certificates/semantic-cuts/order10-skeleton10.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton10.cnf")

semantic_cut_slices_binary cutChunk 10 10 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton10.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order10Skeleton10
