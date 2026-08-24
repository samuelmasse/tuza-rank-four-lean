import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton09

semantic_cut_bundle_binary markedPacking cuts 12 9
  "../../../Certificates/semantic-cuts/order12-skeleton09.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order12-skeleton09.cnf")

semantic_cut_slices_binary cutChunk 12 9 962 512
  "../../../Certificates/semantic-cuts/order12-skeleton09.cutb"

end TuzaRankFour.Certificates.Semantic.Order12Skeleton09
