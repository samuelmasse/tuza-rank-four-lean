import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton03

semantic_cut_bundle_binary markedPacking cuts 9 3
  "../../../Certificates/semantic-cuts/order09-skeleton03.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton03.cnf")

semantic_cut_slices_binary cutChunk 9 3 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton03.cutb"

end TuzaRankFour.Certificates.Semantic.Order09Skeleton03
