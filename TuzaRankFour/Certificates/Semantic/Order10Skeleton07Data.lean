import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton07

semantic_cut_bundle_binary markedPacking cuts 10 7
  "../../../Certificates/semantic-cuts/order10-skeleton07.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton07.cnf")

semantic_cut_slices_binary cutChunk 10 7 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton07.cutb"

end TuzaRankFour.Certificates.Semantic.Order10Skeleton07
