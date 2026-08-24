# Finite certificate layer

The rank-four reduction ends in 66 unsatisfiable DIMACS formulas.  This
directory contains a proof-producing import path for their LRAT certificates.
It does not trust the SAT solver or `drat-trim`: the imported declaration is
an ordinary Lean proof checked by the kernel.

Large LRAT proofs are divided by exhaustive Boolean case splits.  Each leaf
refutes the original formula together with the unit clauses on its path.
`Sat.Fmla.proof_empty_of_split` then removes the units two children at a time,
leaving a proof for the original formula.

`Order10Skeleton06Adaptive` is the current end-to-end reference case.  Its 18
binary LRAT leaves have all been imported and recombined as
`Order10Skeleton06Adaptive.refutation`.  The other 65 cases and the semantic
bridge from the graph statement to these formulas remain to be integrated;
the main theorem must not be described as Lean-verified before that work is
complete.

The importer deliberately avoids `native_decide`, `Lean.ofReduceBool`, and
unchecked external proof declarations.  The reference theorem has only the
standard axioms permitted by Palomar: propositional extensionality, quotient
soundness, and classical choice.
