# Palomar and arXiv release checklist

This repository uses the conventional Palomar root layout: `Challenge.lean`,
`Solution.lean`, `comparator.json`, and `formalization.yaml` are all at the
repository root.

## Release gates

1. Require a green `Full release verification` run at the exact release
   commit. It replays all 66 certificate cases, the axiom audit, Comparator,
   and NanoDa.
2. Require the manuscript PDF and deterministic arXiv source archive to be
   regenerated from that commit.
3. Resolve or explicitly accept the remaining specialist novelty and informal
   exposition review risks recorded in `publication-readiness-2026-08-24.md`.
4. Make the GitHub repository public only after the release commit is frozen.

## Palomar submission

1. Copy the full commit with `git rev-parse HEAD`; do not use an abbreviated
   SHA or a moving branch name.
2. Open <https://submit.palomar-registry.org/> and enter the public repository
   URL and full commit SHA.
3. Leave the optional project, Comparator-config, and metadata paths blank;
   the repository uses Palomar's normal root layout.
4. Declare `responsible author or maintainer` as the authorization relationship.
5. Prefer the browser GitHub sign-in proof of write access. Keep the private
   status-page link returned by Palomar.
6. Read the complete automated review before instructing Palomar to register.
   Registration permanently publishes the immutable record.

Palomar verifies formal statement equality, the permitted axiom set, Lean
kernel replay, and independent NanoDa replay. It does not certify novelty,
importance, or the informal proof.

## arXiv submission

1. Run `python3 scripts/build-arxiv-package.py`.
2. Upload `output/arxiv/tuza-rank-four-arxiv.zip` as a TeX/LaTeX submission and
   select PDFLaTeX if the processor is not detected automatically.
3. Paste the fields from `arxiv/metadata.txt`. Use `math.CO` as the primary
   category and `05C70` as the MSC classification.
4. Choose the arXiv distribution licence deliberately in the submission UI;
   no licence choice is encoded in the source archive.
5. Preview the arXiv-generated PDF and compare all pages, references, and
   tables with `output/pdf/tuza-rank-four.pdf` before the final submit action.
6. The author must self-submit from the author's arXiv account and confirm all
   identity, authorship, policy, and licence declarations.

The arXiv archive intentionally contains only `main.tex` and
`tuza-rank-four.bib`; generated PDFs, auxiliary files, repository certificates,
and development notes do not belong in the TeX upload.
