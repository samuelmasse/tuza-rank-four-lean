import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton06

certificate_locked {
semantic_marked_packing_binary markedPacking 11 6
  "../../../Certificates/semantic-cuts/order11-skeleton06.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order11-skeleton06.cnf")

semantic_cut_slices_binary cutChunk 11 6 730 512
  "../../../Certificates/semantic-cuts/order11-skeleton06.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order11Skeleton06
