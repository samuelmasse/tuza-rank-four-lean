import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton08

semantic_cut_bundle_binary markedPacking cuts 9 8
  "../../../Certificates/semantic-cuts/order09-skeleton08.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton08.cnf")

semantic_cut_slices_binary cutChunk 9 8 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton08.cutb"

end TuzaRankFour.Certificates.Semantic.Order09Skeleton08
