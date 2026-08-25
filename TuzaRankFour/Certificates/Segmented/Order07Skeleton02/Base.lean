import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order08Skeleton00.All

namespace TuzaRankFour.Certificates.Segmented.Order07Skeleton02

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order07-skeleton02.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order07-skeleton02.cnf")

end TuzaRankFour.Certificates.Segmented.Order07Skeleton02
