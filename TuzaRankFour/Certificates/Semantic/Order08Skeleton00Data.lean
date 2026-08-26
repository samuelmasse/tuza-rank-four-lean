import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order08Skeleton00

certificate_locked {
semantic_marked_packing_binary markedPacking 8 0
  "../../../Certificates/semantic-cuts/order08-skeleton00.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order08-skeleton00.cnf")

semantic_cut_slices_binary cutChunk 8 0 264 512
  "../../../Certificates/semantic-cuts/order08-skeleton00.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order08Skeleton00
