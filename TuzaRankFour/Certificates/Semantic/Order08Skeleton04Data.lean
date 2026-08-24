import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order08Skeleton04

semantic_cut_bundle_binary markedPacking cuts 8 4
  "../../../Certificates/semantic-cuts/order08-skeleton04.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order08-skeleton04.cnf")

semantic_cut_slices_binary cutChunk 8 4 264 512
  "../../../Certificates/semantic-cuts/order08-skeleton04.cutb"

end TuzaRankFour.Certificates.Semantic.Order08Skeleton04
