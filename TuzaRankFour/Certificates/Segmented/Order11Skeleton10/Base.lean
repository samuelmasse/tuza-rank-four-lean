import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order11Skeleton07.All

namespace TuzaRankFour.Certificates.Segmented.Order11Skeleton10

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order11-skeleton10.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order11-skeleton10.cnf")

end TuzaRankFour.Certificates.Segmented.Order11Skeleton10
