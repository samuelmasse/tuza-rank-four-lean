import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton11

semantic_cut_bundle_binary markedPacking cuts 10 11
  "../../../Certificates/semantic-cuts/order10-skeleton11.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton11.cnf")

semantic_cut_slices_binary cutChunk 10 11 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton11.cutb"

end TuzaRankFour.Certificates.Semantic.Order10Skeleton11
