# Tuza's conjecture for packing number at most four

[![CI](https://github.com/samuelmasse/tuza-rank-four-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/samuelmasse/tuza-rank-four-lean/actions/workflows/ci.yml)

This repository formalizes the theorem that every finite simple graph `G`
with triangle-packing number `ν(G) ≤ 4` has edge triangle-transversal
number `τ(G) ≤ 2ν(G)`.

The formal definitions use two-element cliques as edges and three-element
cliques as triangles. A packing is a finite family of triangles whose distinct
members intersect in at most one vertex; a transversal is a finite family of
edges such that every triangle contains one of them. The advertised statement
in `Challenge.lean` quantifies over an arbitrary finite vertex type and an
arbitrary `SimpleGraph` on it.

## Verification structure

- `Challenge.lean` contains only the audited definitions and theorem statement.
- `Solution.lean` connects that statement to the proof development.
- `TuzaRankFour/` contains the mathematical proof and certificate interface.
- `comparator.json` fixes the declarations compared by Palomar Comparator.
- `formalization.yaml` records statement provenance, authorship, automation,
  fidelity, and review status.

The planned finite endpoint converts the 66 independently checked DRAT
refutations to LRAT. Mathlib's LRAT importer has been smoke-tested on the
frozen certificates and produces ordinary Lean theorems using only Palomar's
permitted axioms. Parker's theorem through packing rank three, triangle-support
invariance, and the exact isolated-`K₄` and fat-head-crown offsets are proved
in Lean. The rank-four discharging argument and graph-to-certificate bridge
remain ordinary Lean proof obligations.

## Build

The repository pins Lean 4.32.0 and Mathlib 4.32.0.

```text
lake update
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
```

On Linux, the full independent statement check is:

```text
./scripts/verify-comparator.sh
```

## Authorship and assistance

Samuel Masse is the author and responsible maintainer. ChatGPT 5.6 Sol
(OpenAI) and Claude Fable 5 (Anthropic) assisted with research, exposition,
software, and formalization. Samuel Masse is responsible for the mathematical
claims and the released artifact.

## Palomar status

This is a private development repository. A Palomar submission requires a
completed, placeholder-free proof at a fixed commit in a public GitHub
repository. No submission should be made until those conditions and the
independent review gates recorded in `formalization.yaml` are satisfied. The
current submission form is <https://submit.palomar-registry.org/>.

The repository is licensed under Apache-2.0. Cited papers and dependencies
retain their own licences.
