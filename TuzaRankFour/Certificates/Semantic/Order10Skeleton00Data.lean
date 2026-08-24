import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton00

semantic_cut_bundle_binary markedPacking cuts 10 0
  "../../../Certificates/semantic-cuts/order10-skeleton00.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton00.cnf")

semantic_cut_slices_binary cutChunk 10 0 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton00.cutb"

end TuzaRankFour.Certificates.Semantic.Order10Skeleton00
