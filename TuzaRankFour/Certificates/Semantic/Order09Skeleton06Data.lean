import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton06

semantic_cut_bundle_binary markedPacking cuts 9 6
  "../../../Certificates/semantic-cuts/order09-skeleton06.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton06.cnf")

semantic_cut_slices_binary cutChunk 9 6 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton06.cutb"

end TuzaRankFour.Certificates.Semantic.Order09Skeleton06
