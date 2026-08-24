import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order10Skeleton02.All

namespace TuzaRankFour.Certificates.Segmented.Order09Skeleton05

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order09-skeleton05.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order09-skeleton05.cnf")

end TuzaRankFour.Certificates.Segmented.Order09Skeleton05
