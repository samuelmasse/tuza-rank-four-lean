# Lean buddy log

This log tracks the source-aligned all-rank formalization.  It is separate
from the rank-four publication theorem and its finite certificates.

## 2026-08-26 — wave 1: generic reduction spine

Source records audited:

- `tuza-closure-first-resource-clutter-augmenter-blocker-discovery-2026-08-26.md`
- `tuza-literal-multi-contact-triangle-blocker-augmenter-discovery-2026-08-26.md`
- `tuza-three-owner-four-for-three-trade-blocker-discovery-2026-08-26.md`
- `tuza-isolated-three-owner-plus-one-brace-interaction-discovery-2026-08-26.md`
- `tuza-two-three-owner-same-three-members-discovery-2026-08-26.md`

Implemented statements:

- literal ground-edge deletion `SimpleGraph.deleteEdgeFinset`;
- `IsExactRankBlocker`, with exact damage recorded as
  `ν(G.deleteEdgeFinset C) + d = ν(G)`;
- positive strength-two `IsTuzaReducer` and the exposed conditional
  `HasUnavoidableTuzaReduction`;
- same-source transversal lift by `C ∪ D`;
- the generic reducer implication in numerical and explicit-cover forms;
- well-founded packing-rank induction from unavoidable reducers to Tuza;
- maximum-packing-witness-bound owner, one-contact, brace, three-owner,
  contact-closure, and owner-closed-region definitions.

Translation decisions and open mismatches:

- Lean owners are packed triangles rather than numeric indices.  This removes
  a relabeling layer while preserving the source definition
  `E(H) ∩ E(P_i) ≠ ∅` as `2 ≤ |H ∩ P_i|` for literal triangles.
- `IsOwnerClosed` formalizes the whole-component closure implication but not
  connectedness.  A later contact-component API must add connectivity without
  weakening owner closure.
- The local one-contact, two-cell brace, isolated three-owner, and mixed
  three-owner-plus-one-brace papers still require exact Lean predicates before
  their blocker constructions can be encoded.  No hypotheses from those
  papers have been invented here.

Next obligations:

1. prove the exact triangle-survival iff and owner/ground-edge equivalence;
2. formalize contact-graph connectivity and component saturation;
3. encode the one-contact blocker as the first local atom;
4. encode the unique-three-owner-per-owner-triple theorem, which is a small
   source-level structural result independent of the omission CSP.
