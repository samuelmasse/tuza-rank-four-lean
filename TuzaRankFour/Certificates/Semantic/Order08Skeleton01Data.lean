import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order08Skeleton01

certificate_locked {
semantic_marked_packing_binary markedPacking 8 1
  "../../../Certificates/semantic-cuts/order08-skeleton01.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order08-skeleton01.cnf")

semantic_cut_slices_binary cutChunk 8 1 264 512
  "../../../Certificates/semantic-cuts/order08-skeleton01.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order08Skeleton01
