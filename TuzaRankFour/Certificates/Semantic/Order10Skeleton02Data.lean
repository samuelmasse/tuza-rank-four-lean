import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton02

semantic_cut_bundle_binary markedPacking cuts 10 2
  "../../../Certificates/semantic-cuts/order10-skeleton02.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton02.cnf")

semantic_cut_slices_binary cutChunk 10 2 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton02.cutb"

end TuzaRankFour.Certificates.Semantic.Order10Skeleton02
