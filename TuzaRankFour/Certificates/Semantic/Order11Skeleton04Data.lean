import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton04

semantic_cut_bundle_binary markedPacking cuts 11 4
  "../../../Certificates/semantic-cuts/order11-skeleton04.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton04.cnf")

semantic_cut_slices_binary cutChunk 11 4 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton04.cutb"

end TuzaRankFour.Certificates.Semantic.Order11Skeleton04
