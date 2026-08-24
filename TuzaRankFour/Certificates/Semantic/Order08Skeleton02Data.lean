import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order08Skeleton02

semantic_cut_bundle_binary markedPacking cuts 8 2
  "../../../Certificates/semantic-cuts/order08-skeleton02.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order08-skeleton02.cnf")

semantic_cut_slices_binary cutChunk 8 2 264 512
  "../../../Certificates/semantic-cuts/order08-skeleton02.cutb"

end TuzaRankFour.Certificates.Semantic.Order08Skeleton02
