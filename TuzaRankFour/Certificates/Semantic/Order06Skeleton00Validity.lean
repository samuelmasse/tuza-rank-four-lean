import TuzaRankFour.Certificates.Semantic.Order06Skeleton00Data

namespace TuzaRankFour.Certificates.Semantic.Order06Skeleton00

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cuts_valid : cutsValidBool 6 cuts = true := by decide

end TuzaRankFour.Certificates.Semantic.Order06Skeleton00
