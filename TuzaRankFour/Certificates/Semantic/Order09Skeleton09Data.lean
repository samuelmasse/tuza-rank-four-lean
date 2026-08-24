import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton09

semantic_cut_bundle_binary markedPacking cuts 9 9
  "../../../Certificates/semantic-cuts/order09-skeleton09.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton09.cnf")

semantic_cut_slices_binary cutChunk 9 9 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton09.cutb"

end TuzaRankFour.Certificates.Semantic.Order09Skeleton09
