import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order10Skeleton06.All

namespace TuzaRankFour.Certificates.Segmented.Order10Skeleton13

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order10-skeleton13.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order10-skeleton13.cnf")

end TuzaRankFour.Certificates.Segmented.Order10Skeleton13
