import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order09Skeleton08.All

namespace TuzaRankFour.Certificates.Segmented.Order09Skeleton09

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order09-skeleton09.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order09-skeleton09.cnf")

end TuzaRankFour.Certificates.Segmented.Order09Skeleton09
