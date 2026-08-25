import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order11Skeleton02.All

namespace TuzaRankFour.Certificates.Segmented.Order10Skeleton06

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order10-skeleton06.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order10-skeleton06.cnf")

end TuzaRankFour.Certificates.Segmented.Order10Skeleton06
