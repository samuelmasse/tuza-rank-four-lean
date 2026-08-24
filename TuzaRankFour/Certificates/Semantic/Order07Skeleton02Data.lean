import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order07Skeleton02

semantic_cut_bundle_binary markedPacking cuts 7 2
  "../../../Certificates/semantic-cuts/order07-skeleton02.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order07-skeleton02.cnf")

semantic_cut_slices_binary cutChunk 7 2 172 512
  "../../../Certificates/semantic-cuts/order07-skeleton02.cutb"

end TuzaRankFour.Certificates.Semantic.Order07Skeleton02
