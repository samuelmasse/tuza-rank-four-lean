import TuzaRankFour.Certificates.Semantic.Order12Skeleton04Data

namespace TuzaRankFour.Certificates.Semantic.Order12Skeleton04

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cuts_valid : cutsValidBool 12 cuts = true := by decide

end TuzaRankFour.Certificates.Semantic.Order12Skeleton04
