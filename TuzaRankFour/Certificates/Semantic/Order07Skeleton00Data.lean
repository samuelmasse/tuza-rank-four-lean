import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order07Skeleton00

semantic_cut_bundle_binary markedPacking cuts 7 0
  "../../../Certificates/semantic-cuts/order07-skeleton00.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order07-skeleton00.cnf")

semantic_cut_slices_binary cutChunk 7 0 172 512
  "../../../Certificates/semantic-cuts/order07-skeleton00.cutb"

end TuzaRankFour.Certificates.Semantic.Order07Skeleton00
