import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order07Skeleton01

semantic_cut_bundle_binary markedPacking cuts 7 1
  "../../../Certificates/semantic-cuts/order07-skeleton01.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order07-skeleton01.cnf")

semantic_cut_slices_binary cutChunk 7 1 172 512
  "../../../Certificates/semantic-cuts/order07-skeleton01.cutb"

end TuzaRankFour.Certificates.Semantic.Order07Skeleton01
