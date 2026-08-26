import TuzaRankFour.Certificates.SemanticCutBinary

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton10

certificate_locked {
semantic_marked_packing_binary markedPacking 12 10
  "../../../Certificates/semantic-cuts/order12-skeleton10.cutb"

dimacs_formula_chunks formulaChunk 512
  (include_str "../../../Certificates/cnf/order12-skeleton10.cnf")

semantic_cut_slices_binary cutChunk 12 10 962 512
  "../../../Certificates/semantic-cuts/order12-skeleton10.cutb"
}

end TuzaRankFour.Certificates.Semantic.Order12Skeleton10
