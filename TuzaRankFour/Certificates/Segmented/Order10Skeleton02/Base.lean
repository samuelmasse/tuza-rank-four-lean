import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order10Skeleton10.All

namespace TuzaRankFour.Certificates.Segmented.Order10Skeleton02

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order10-skeleton02.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order10-skeleton02.cnf")

end TuzaRankFour.Certificates.Segmented.Order10Skeleton02
