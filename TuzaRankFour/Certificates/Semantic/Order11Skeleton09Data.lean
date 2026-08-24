import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton09

semantic_cut_bundle_binary markedPacking cuts 11 9
  "../../../Certificates/semantic-cuts/order11-skeleton09.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton09.cnf")

semantic_cut_slices_binary cutChunk 11 9 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton09.cutb"

end TuzaRankFour.Certificates.Semantic.Order11Skeleton09
