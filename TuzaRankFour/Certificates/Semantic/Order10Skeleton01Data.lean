import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order10Skeleton01

semantic_cut_bundle_binary markedPacking cuts 10 1
  "../../../Certificates/semantic-cuts/order10-skeleton01.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order10-skeleton01.cnf")

semantic_cut_slices_binary cutChunk 10 1 539 512
  "../../../Certificates/semantic-cuts/order10-skeleton01.cutb"

end TuzaRankFour.Certificates.Semantic.Order10Skeleton01
