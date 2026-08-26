import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order06Skeleton00

certificate_locked {
semantic_marked_packing_binary markedPacking 6 0
  "../../../Certificates/semantic-cuts/order06-skeleton00.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order06-skeleton00.cnf")

semantic_cut_slices_binary cutChunk 6 0 105 512
  "../../../Certificates/semantic-cuts/order06-skeleton00.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order06Skeleton00
