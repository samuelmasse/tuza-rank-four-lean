import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order12Skeleton11.All

namespace TuzaRankFour.Certificates.Segmented.Order12Skeleton08

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order12-skeleton08.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order12-skeleton08.cnf")

end TuzaRankFour.Certificates.Segmented.Order12Skeleton08
