import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order12Skeleton08.All

namespace TuzaRankFour.Certificates.Segmented.Order12Skeleton04

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order12-skeleton04.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order12-skeleton04.cnf")

end TuzaRankFour.Certificates.Segmented.Order12Skeleton04
