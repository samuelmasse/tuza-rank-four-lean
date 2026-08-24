import Mathlib.Tactic.Sat.FromLRAT

/-!
# Exhaustive certificate partitions

An LRAT leaf may refute a DIMACS formula after adjoining a path of unit
clauses.  The lemma below removes one Boolean split.  Repeated applications
combine any finite binary decision tree of kernel-checked leaf refutations
into a refutation of the unsplit formula.
-/

namespace Sat.Fmla

/-- If both truth values of one SAT variable refute a formula, then the
formula itself is refutable. -/
theorem proof_empty_of_split (f : Sat.Fmla) (index : Nat)
    (negative : (f.and (Sat.Fmla.one [Sat.Literal.neg index])).proof [])
    (positive : (f.and (Sat.Fmla.one [Sat.Literal.pos index])).proof []) :
    f.proof [] := by
  intro valuation satisfies
  by_cases value : valuation index
  · apply positive valuation
    refine ⟨fun clause member => ?_⟩
    rcases List.mem_append.mp member with member | member
    · exact satisfies.prop clause member
    · simp only [Sat.Fmla.one, List.mem_singleton] at member
      subst clause
      exact fun absent => absent value
  · apply negative valuation
    refine ⟨fun clause member => ?_⟩
    rcases List.mem_append.mp member with member | member
    · exact satisfies.prop clause member
    · simp only [Sat.Fmla.one, List.mem_singleton] at member
      subst clause
      exact value

end Sat.Fmla
