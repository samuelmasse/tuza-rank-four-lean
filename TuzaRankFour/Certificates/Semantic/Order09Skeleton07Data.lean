import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton07

semantic_cut_bundle_binary markedPacking cuts 9 7
  "../../../Certificates/semantic-cuts/order09-skeleton07.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton07.cnf")

semantic_cut_slices_binary cutChunk 9 7 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton07.cutb"

end TuzaRankFour.Certificates.Semantic.Order09Skeleton07
