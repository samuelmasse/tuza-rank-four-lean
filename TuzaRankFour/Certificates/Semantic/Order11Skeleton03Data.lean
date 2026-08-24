import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton03

semantic_cut_bundle_binary markedPacking cuts 11 3
  "../../../Certificates/semantic-cuts/order11-skeleton03.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton03.cnf")

semantic_cut_slices_binary cutChunk 11 3 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton03.cutb"

end TuzaRankFour.Certificates.Semantic.Order11Skeleton03
