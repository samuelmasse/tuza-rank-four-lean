import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order10Skeleton00.All

namespace TuzaRankFour.Certificates.Segmented.Order09Skeleton00

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order09-skeleton00.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order09-skeleton00.cnf")

end TuzaRankFour.Certificates.Segmented.Order09Skeleton00
