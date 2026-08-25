import TuzaRankFour.Certificates.CheckpointLRAT
import TuzaRankFour.Certificates.Segmented.Order12Skeleton13.All

namespace TuzaRankFour.Certificates.Segmented.Order11Skeleton14

dimacs_formula_binary formula
  (include_str "../../../../Certificates/cnf/order11-skeleton14.cnf")

dimacs_initial_clause_bundle initialClauses
  formula
  (include_str "../../../../Certificates/cnf/order11-skeleton14.cnf")

end TuzaRankFour.Certificates.Segmented.Order11Skeleton14
