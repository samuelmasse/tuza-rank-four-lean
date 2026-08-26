import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton00

certificate_locked {
semantic_marked_packing_binary markedPacking 11 0
  "../../../Certificates/semantic-cuts/order11-skeleton00.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton00.cnf")

semantic_cut_slices_binary cutChunk 11 0 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton00.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton00
