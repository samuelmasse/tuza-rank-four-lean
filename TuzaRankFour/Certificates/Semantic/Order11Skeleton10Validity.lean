import TuzaRankFour.Certificates.Semantic.Order11Skeleton10Data

namespace TuzaRankFour.Certificates.Semantic.Order11Skeleton10

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cuts_valid : cutsValidBool 11 cuts = true := by decide

end TuzaRankFour.Certificates.Semantic.Order11Skeleton10
