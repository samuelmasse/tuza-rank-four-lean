import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton10

semantic_cut_bundle_binary markedPacking cuts 9 10
  "../../../Certificates/semantic-cuts/order09-skeleton10.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order09-skeleton10.cnf")

semantic_cut_slices_binary cutChunk 9 10 385 512
  "../../../Certificates/semantic-cuts/order09-skeleton10.cutb"

end TuzaRankFour.Certificates.Semantic.Order09Skeleton10
