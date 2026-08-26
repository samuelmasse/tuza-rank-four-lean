# Publication readiness and formalization record

Date: 24 August 2026

Scope: the rank-four theorem only

Current status: the complete theorem compiles in Lean; independent
Comparator/NanoDa replay, clean-checkout replay, and specialist review remain
publication gates.

## Frozen theorem

All graphs are finite, undirected, loopless, and simple. A triangle is a
three-vertex clique. A triangle packing is a family of triangles whose graph
edge sets are pairwise disjoint, and \(\nu(G)\) is its maximum cardinality. A
triangle transversal is a set of graph edges meeting every triangle, and
\(\tau(G)\) is its minimum cardinality.

The theorem proved in this repository is:

> For every finite simple graph \(G\), if \(\nu(G)\leq4\), then
> \(\tau(G)\leq2\nu(G)\).

The quantifier ranges over arbitrary finite vertex types. The statement uses
edge-disjoint, not vertex-disjoint, packings. The separate candidate
strengthening for \(K_4\)-free graphs with \(\nu(G)=4\) and \(\tau(G)\leq7\)
is intentionally excluded.

## Proof dependency graph

The shortest dependency chain from the definitions is:

    finite graph definitions
      |
      +-- packing rank at most three
      |     direct formalization of Parker's argument
      |
      +-- assume nu(G) = 4 and tau(G) > 8
            |
            +-- triangle support and canonical vertex splitting
            |     preserve nu and do not decrease tau
            |
            +-- isolated-K4 and fat-head-crown reductions
            |     exact packing/transversal offsets
            |
            +-- saturated four-packing and discharging
            |     the reduced support has at most 12 vertices
            |
            +-- classify the marked four-packing
            |     16 incidence types, 66 cumulative order/type cases
            |
            +-- for each case:
            |     validate exact five-packing/eight-cover cuts
            |     identify the reconstructed formula with the frozen CNF
            |     replay its LRAT refutation
            |
            +-- contradiction

The final composition is SimpleGraph.tuza_rank_four_proof in
TuzaRankFour/Main.lean. Solution.lean exposes the corresponding Palomar
declaration SimpleGraph.tuza_rank_four.

## Evidence and trust boundary

| Layer | Repository evidence | Trust boundary |
|---|---|---|
| Analytic mathematics | Direct Lean proofs of the finite graph definitions, Parker rank-three theorem, support reduction, splitting, crown and isolated-\(K_4\) offsets, discharge, and twelve-vertex bound | Lean kernel, imported Mathlib declarations, and the standard permitted axioms |
| Finite exhaustive claim | Direct classification of valid four-block incidence families into sixteen canonical types; seven order endpoints; exact 66-case dispatch | Lean kernel and the reflected finite computations |
| Statement translation | Lean parses the compact semantic records, verifies every packing or cover witness, rebuilds all clauses, and proves equality with each frozen CNF | Lean source defining the graph/CNF interpretation and the frozen data files |
| Solver certificates | 66 final formulas, 572 binary LRAT segments, and kernel-checked refutation theorems | Mathlib's LRAT importer, Lean kernel, and certificate bytes |
| Producer software | SAT generation, Python witness generation, DRAT production, DRAT-to-LRAT conversion | Not trusted; only the checked outputs enter the theorem |
| Independent statement comparison | Palomar Challenge/Solution configuration and axiom audit | Local axiom audit passes; Comparator and NanoDa replay remain to be run from a clean Linux environment |

Routine CI intentionally stops at the complete analytic endpoint, one
representative semantic reconstruction, and one LRAT segment. The full 66-case
replay is the separately dispatched `Full release verification` workflow on a
high-memory self-hosted Linux runner. A green routine-CI badge is therefore
not, by itself, release evidence.

The finite layer contains 331,430 semantic records: 231,947 five-packing cuts
and 99,483 cover cuts. The original DRAT traces contain 570,595,138 bytes. The
checked proof source uses 572 binary LRAT segments occupying 250.98 MiB.

The axiom audit on 24 August 2026 reported, for both the advertised theorem
and the carrier-independent finite endpoint:

    [propext, Classical.choice, Quot.sound]

No Solution declaration depends on sorryAx, Lean.ofReduceBool, native_decide,
or a custom axiom. Challenge.lean contains the single deliberate statement
hole prescribed by the Palomar Challenge/Solution format; Comparator is
required to show that the Solution theorem with the same type has no such
dependency.

## Hostile gap audit

There is no remaining admitted mathematical lemma in the Solution proof. The
weakest current verification step is no longer a graph-theoretic reduction or
a SAT semantic clause: it is independent reconstruction of the complete
repository boundary.

The remaining risks, in order, are:

1. Comparator and NanoDa have not yet replayed the exact final commit.
2. The final commit has not yet been built from an empty Lake build directory
   on an independent machine.
3. A specialist has not audited the short Challenge definitions against the
   standard graph-theoretic meanings of \(\nu\) and \(\tau\), nor checked that
   the prose proof accurately describes the Lean dependency chain.
4. The manuscript has not received external mathematical or editorial review.
5. Novelty remains unresolved.

The most delicate human-readable section remains the discharging transfer
from a reduced strict counterexample to the twelve-vertex kernel. Lean checks
that argument, but a paper referee still needs an intelligible exposition
rather than being asked to read proof terms. The most delicate artifact
section is the graph-to-CNF bridge; it is now formal, but reviewers should
still inspect its definitions because a formal proof establishes the encoded
statement.

Failure of any LRAT segment, semantic equality, canonical-case match, axiom
audit, Comparator check, or clean build is a release-stopping defect.

## Primary-source literature search

The search was refreshed on 24 August 2026. Exact and synonymous searches
included “triangle packing number at most four,” “at most four edge-disjoint
triangles,” “no five edge-disjoint triangles,” and the formula
\(\nu(G)\leq4\Rightarrow\tau(G)\leq2\nu(G)\). Searches covered arXiv, publisher
pages, the Electronic Journal of Combinatorics, and general web indexing.
MathSciNet, zbMATH, and Scopus were not searched, and no specialist was
consulted.

Primary sources opened and checked include:

- Alex Parker, [New bounds on a generalization of Tuza's
  conjecture](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i2p20/pdf/),
  Electronic Journal of Combinatorics 32(2) (2025), P2.20. Theorems 2 and 3
  and Corollary 4 appear on printed page 3. Corollary 4 gives the exact
  \(\nu(G)\leq3\) graph boundary and does not state rank four.
- Zimo Sheng and Mingyu Xiao, [A discharging method: improved kernels for
  edge triangle packing and
  covering](https://arxiv.org/pdf/2308.16515v1), arXiv:2308.16515v1.
  Lemma 3 is on printed pages 4--5, vertex splitting is Reduction Rule 4 and
  Lemma 4 on printed page 6, and the discharging analysis begins in Section 5
  on printed page 8. The journal version is
  [Theoretical Computer Science 1004 (2024),
  114635](https://doi.org/10.1016/j.tcs.2024.114635). These sources prove
  separate \(3k\)-vertex kernels for the two parameterized decision problems;
  they do not state the rank-four theorem or the exact joint optimum
  composition used here.
- Zsolt Tuza, [A conjecture on triangles of
  graphs](https://doi.org/10.1007/BF01787705), Graphs and Combinatorics 6
  (1990), 373--380, is the historical source for the conjecture and several
  graph-class results.
- Penny Haxell, [Packing and covering triangles in
  graphs](https://doi.org/10.1016/S0012-365X(98)00183-6), Discrete
  Mathematics 195 (1999), 251--254, proves the universal \(66/23\) bound.
- Anish Gupta, [Tuza's conjecture for graphs of maximum degree at most
  seven](https://arxiv.org/pdf/2608.06538), arXiv:2608.06538v1. Theorem 1.3
  appears on printed page 2 and concerns the class \(\Delta(G)\leq7\), not a
  bounded packing number.

No exact primary-source match for the frozen rank-four theorem was located.
This is an absence report, not a novelty or priority verdict. The manuscript
must not use “first,” “new,” or “novel” until subscription-database searching
and a knowledgeable specialist review are complete.

## Formalization design

The representation uses finite vertex finsets:

- triangles are three-element cliques;
- graph edges are two-element cliques;
- pairwise edge-disjointness is expressed by triangle intersections of
  cardinality at most one;
- a transversal is a finite set of graph edges, each represented as a
  two-element subset of a triangle.

The analytic mathematics is formalized directly. The sixteen-family
classification uses small reflected finite theorems. The 66 large
propositional endpoints are checked through certificate reflection, which is
substantially smaller and more auditable than manually encoding each solver
search.

Mathlib supplied the finite simple graph, clique, finite-set, Hall, and LRAT
infrastructure. Project-specific infrastructure was required for Tuza
extrema, triangle support, canonical splitting, packing saturation, crowns,
the discharge ledger, incidence-family classification, graph relabelling, and
the semantic CNF interpretation.

The initial minimum smoke target was the edge-based \(K_4\) representation
and one order-six LRAT import. Subsequent explicit authorization expanded the
scope to the complete theorem. The order-six import, all 66 endpoints, the
carrier-independent endpoint, and the final theorem now compile, so a separate
smoke-only artifact is no longer the limiting representation test.

## Paper boundaries

The rank-four result should be a separate computer-assisted graph theory
paper. The line-graph and triangle-free-root total-graph theorems belong
together in a different analytic paper because they share a local-clique and
parity architecture. Cones, ports, false-twin profiles, and related
construction material should appear nowhere in the initial papers: they are
not needed corollaries and have not passed equivalent proof and novelty gates.

## Release decisions

### Paper draft

GO: maintain and circulate a private draft that states the exact theorem,
separates the analytic and finite parts, gives the full certificate contract,
and describes novelty only as unresolved.

PARK: journal submission until Comparator/NanoDa, clean-checkout replay,
specialist mathematical review, and a broader novelty search pass.

STOP: withdraw the theorem from the paper if the Lean theorem ceases to build,
the Challenge statement is found to mistranslate the graph invariant, or any
certificate/formula identity fails.

### Lean artifact

GO: continue focused cleanup, deterministic rebuild instructions, axiom audit,
and independent Comparator/NanoDa verification.

PARK: declaring the artifact independently verified until the exact final
commit passes those checks from a clean Linux checkout.

STOP: do not replace checked certificate reflection with unchecked solver
output, trusted native evaluation, or a custom axiom.

### Expert review

GO: prepare a reviewer packet containing the manuscript, exact Challenge
statement, proof DAG, certificate manifest, axiom report, and clean replay
commands.

PARK: contacting a reviewer until the final private commit and rendered PDF
are frozen, in accordance with the current no-contact instruction.

STOP: public correctness or novelty language if a reviewer finds a statement
translation defect, an unreported trust dependency, or prior art that
subsumes the theorem.

### Public artifact and Palomar

GO: only after the repository is intentionally made public, the exact public
commit passes Palomar's mechanical checks, all consumed source is under the
500 MiB checkout limit, and Samuel Masse explicitly authorizes submission.

PARK: public release and Palomar registration now. The repository is private,
novelty is unresolved, and external review is pending.

STOP: any automatic submission, publicity, or priority claim. Mechanical
verification would establish only that the Solution proves the Challenge
under the recorded trust boundary; it would not establish novelty or journal
acceptance.

## Next editorial action

Finish a clean Linux Comparator/NanoDa replay of the frozen private commit,
then prepare the specialist reviewer packet. No submission, public release,
or novelty claim should precede those steps.
