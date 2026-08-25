import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order12Skeleton03.All

namespace TuzaRankFour.Certificates.Segmented.Order12Skeleton05

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order12-skeleton05.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order12-skeleton05.cnf")

end TuzaRankFour.Certificates.Segmented.Order12Skeleton05
