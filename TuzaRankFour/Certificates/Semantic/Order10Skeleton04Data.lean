import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton04

semantic_cut_bundle_binary markedPacking cuts 10 4
  "../../../Certificates/semantic-cuts/order10-skeleton04.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton04.cnf")

semantic_cut_slices_binary cutChunk 10 4 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton04.cutb"

end TuzaRankFour.Certificates.Semantic.Order10Skeleton04
