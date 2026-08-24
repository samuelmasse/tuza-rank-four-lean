import TuzaRankFour.Certificates.CheckpointLRAT

namespace TuzaRankFour.Certificates.Segmented.Order12Skeleton11

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order12-skeleton11.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order12-skeleton11.cnf")

end TuzaRankFour.Certificates.Segmented.Order12Skeleton11
