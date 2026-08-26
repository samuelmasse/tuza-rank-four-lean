import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton01

certificate_locked {
semantic_marked_packing_binary markedPacking 11 1
  "../../../Certificates/semantic-cuts/order11-skeleton01.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton01.cnf")

semantic_cut_slices_binary cutChunk 11 1 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton01.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton01
