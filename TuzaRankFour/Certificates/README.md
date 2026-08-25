# Finite certificate layer

The rank-four reduction ends in 66 unsatisfiable DIMACS formulas.  This
directory contains a proof-producing import path for their LRAT certificates.
It does not trust the SAT solver or `drat-trim`: the imported declaration is
an ordinary Lean proof checked by the kernel.

Large LRAT proofs are divided by exhaustive Boolean case splits.  Each leaf
refutes the original formula together with the unit clauses on its path.
`Sat.Fmla.proof_empty_of_split` then removes the units two children at a time,
leaving a proof for the original formula.

`DirectSmall` imports all 21 order-six through order-nine cases.  Every larger
case is divided into binary LRAT segments and recombined by repeated Boolean
case splitting.  Across the 66 cases, Lean checks 572 segments and derives one
refutation theorem for each final formula.  The semantic layer independently
reconstructs all packing and covering witnesses, checks the resulting clauses
against the exact formulas, and connects the 66 refutations to the finite
graph endpoint used by the main theorem.

The importer deliberately avoids `native_decide`, `Lean.ofReduceBool`, and
unchecked external proof declarations.  The advertised theorem has only the
standard axioms permitted by Palomar: propositional extensionality, quotient
soundness, and classical choice.
