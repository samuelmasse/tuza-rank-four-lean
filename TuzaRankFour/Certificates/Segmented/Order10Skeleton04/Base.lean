import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order11Skeleton01.All

namespace TuzaRankFour.Certificates.Segmented.Order10Skeleton04

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order10-skeleton04.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order10-skeleton04.cnf")

end TuzaRankFour.Certificates.Segmented.Order10Skeleton04
