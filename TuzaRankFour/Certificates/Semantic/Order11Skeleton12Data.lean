import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton12

semantic_cut_bundle_binary markedPacking cuts 11 12
  "../../../Certificates/semantic-cuts/order11-skeleton12.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton12.cnf")

semantic_cut_slices_binary cutChunk 11 12 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton12.cutb"

end TuzaRankFour.Certificates.Semantic.Order11Skeleton12
