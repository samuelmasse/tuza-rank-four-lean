import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton04

semantic_cut_bundle_binary markedPacking cuts 9 4
  "../../../Certificates/semantic-cuts/order09-skeleton04.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton04.cnf")

semantic_cut_slices_binary cutChunk 9 4 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton04.cutb"

end TuzaRankFour.Certificates.Semantic.Order09Skeleton04
