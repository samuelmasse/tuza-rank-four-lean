import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton02

semantic_cut_bundle_binary markedPacking cuts 11 2
  "../../../Certificates/semantic-cuts/order11-skeleton02.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton02.cnf")

semantic_cut_slices_binary cutChunk 11 2 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton02.cutb"

end TuzaRankFour.Certificates.Semantic.Order11Skeleton02
