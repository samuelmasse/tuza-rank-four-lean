import TuzaRankFour.Certificates.Semantic.Order09Skeleton08Data

namespace TuzaRankFour.Certificates.Semantic.Order09Skeleton08

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cuts_valid : cutsValidBool 9 cuts = true := by decide

end TuzaRankFour.Certificates.Semantic.Order09Skeleton08
