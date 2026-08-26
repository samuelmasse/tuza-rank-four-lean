# Tuza's conjecture for packing number at most four

[![CI](https://github.com/samuelmasse/tuza-rank-four-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/samuelmasse/tuza-rank-four-lean/actions/workflows/ci.yml)

This repository proves in Lean that every finite simple graph \(G\) with
triangle-packing number \(\nu(G)\leq 4\) has an edge set meeting every triangle
whose cardinality is at most \(2\nu(G)\).

A triangle packing is a family of pairwise edge-disjoint triangles. A triangle
transversal is a set of graph edges meeting every triangle. The compared
declaration is:

    theorem SimpleGraph.tuza_rank_four
        {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V)
        (hν : G.trianglePackingNumber ≤ 4) :
        G.triangleTransversalNumber ≤ 2 * G.trianglePackingNumber

The stronger statement for \(K_4\)-free graphs with \(\nu(G)=4\) and
\(\tau(G)\leq 7\) is not part of this repository.

## Proof structure

The proof has an analytic reduction and a certified finite endpoint.

1. Parker's packing-rank-three argument is formalized directly.
2. A strict rank-four counterexample is replaced by a triangle-supported,
   split-normal kernel with the same packing number, no smaller transversal
   number, and at most twelve vertices.
3. The incidence family of a marked maximum four-packing is classified into
   sixteen canonical types. Across orders six through twelve this gives 66
   labelled cases.
4. Each case has a SAT formula whose semantic cuts come from exact
   five-packing or eight-transversal witnesses. Lean reconstructs and validates
   all 331,430 cuts and checks their exact agreement with the final formulas.
5. Each final formula is refuted by a kernel-checked LRAT proof. The 66 proofs
   are stored as 572 binary segments.
6. The canonical-packing dispatch connects those refutations to the finite
   graph theorem, which is then composed with the analytic reduction.

The SAT solver, witness generator, and DRAT-to-LRAT converter are not trusted:
their outputs are checked in Lean. The advertised theorem uses exactly
propext, Classical.choice, and Quot.sound, the three axioms permitted by
Palomar. It does not use sorryAx, Lean.ofReduceBool, native_decide, or a custom
axiom.

## Repository layout

- Challenge.lean is the short, Mathlib-only statement of record. Its deliberate
  theorem hole is allowed by the Palomar Challenge/Solution format.
- Solution.lean supplies the proof of the compared theorem.
- TuzaRankFour/Analytic.lean is the lightweight proof boundary through the
  twelve-vertex reduction. TuzaRankFour/Finite.lean is the heavy boundary that
  imports the exhaustive classification and certificates; Main.lean composes
  the two layers.
- Certificates/ contains the frozen CNFs, compact semantic witnesses, binary
  LRAT segments, and manifests.
- paper/ contains the article source; the rendered article is placed in
  output/pdf/.
- comparator.json fixes the declarations and permitted axioms checked by
  Palomar Comparator.
- formalization.yaml records provenance, authorship, automation, fidelity, and
  review status.
- docs/publication-readiness-2026-08-24.md records the proof boundary,
  literature search, hostile audit, and release gates.

## Verification

The project pins Lean 4.32.0 and Mathlib 4.32.0. The ordinary contributor loop
builds the challenge, the complete analytic layer, and one representative
semantic/LRAT case without replaying the 66-case certificate corpus:

    lake update
    lake exe cache get
    lake build
    lake build +TuzaRankFour.Analytic
    lake build +TuzaRankFour.Certificates.Semantic.Order06Skeleton00

A clean release build is deliberately substantial: it replays every proof
certificate, takes longer than GitHub's six-hour hosted-job limit, and produces
about 36 GiB of Lake artifacts.

    lake build Solution
    lake env lean TuzaRankFour/Audit.lean
    ruby scripts/validate-formalization.rb

On Linux, the independent statement comparison and NanoDa replay are:

    ./scripts/verify-comparator.sh

The manually dispatched `Full release verification` workflow runs that replay
on a Linux self-hosted runner labelled `tuza-release`. The runner must have at
least 48 GiB of RAM, 80 GiB of free workspace storage, and Cargo installed.
The workflow splits the four LRAT lanes and four semantic shards into separate
steps so GitHub does not kill a monolithic six-hour step.

TuzaRankFour/Audit.lean prints the axiom set for both the advertised theorem
and the carrier-independent finite endpoint.

## Authorship

Samuel Masse is the author and responsible maintainer. ChatGPT 5.6 Sol
(OpenAI) and Claude Fable 5 (Anthropic) assisted with research, exposition,
software, and formalization. Samuel Masse checked their output and is
responsible for the mathematical claims and released artifact.

## Publication and Palomar status

The repository remains private while the manuscript and artifact undergo
independent review. A targeted primary-source search found no exact statement
of the rank-four theorem, but absence of a match is not a novelty verdict.
Neither the paper nor this repository should claim priority before a
specialist literature review.

Palomar requires a completed proof at a fixed commit in a public GitHub
repository. No submission or public release is authorized yet. The submission
portal is <https://submit.palomar-registry.org/>.

The repository is licensed under Apache-2.0. Cited papers and dependencies
retain their own licences.
