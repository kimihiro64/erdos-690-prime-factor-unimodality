# Erdos 690: Prime-Factor Density Unimodality

[![CI](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/actions/workflows/ci.yml/badge.svg)](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/actions/workflows/ci.yml)

Lean formalization of the finite density recursion and unimodality classification
for ordered distinct prime factors.

## Problem

**Unimodality of the density of the kth smallest distinct prime factor**

For each integer k at least 1 and prime p, let d_k(p) be the natural density of positive integers whose kth smallest distinct prime divisor is p. Classify those k for which the prime-indexed sequence p mapsto d_k(p) is unimodal.

## Current status

The repository defines Cambie's exact finite density recursion, identifies it
with natural density, and proves the positive unimodality cases `k ≤ 3`.
Exact generated certificates prove non-unimodality for every `4 ≤ k ≤ 20`;
certified fixed-point weight sums, explicit prime gaps, and symmetric-sum
bounds extend this to every `21 ≤ k ≤ 48`.

The current large-range development contains a closed composite-block
certificate, generated kernel-replayable record-twin certificates, a finite
prime-prefix/reciprocal-sum route through `k = 38,000`, and a uniform-tail
reduction. The public Challenge/Solution boundary now states the exact
universal all-`k` theorem, but the Solution proof is not yet unconditional:
its remaining boundary consists of the generated certificates still being
built and the explicit analytic prime-estimate interfaces. See
[`TODO.md`](TODO.md) for the completion gates. This checkpoint therefore does
not yet claim a complete formalization of Erdős 690.

The release state is visible mechanically:

- while `formalization.yaml` contains the canonical `TEMPLATE:` sentinels, CI
  validates the starter surface but the repository is not submission-ready;
- after the real metadata and Challenge/Solution surface replace every
  sentinel, CI enforces the ordinary Palomar metadata contract.

## Repository map

- `Challenge.lean` — small human-auditable statement surface.
- `Solution.lean` — corresponding proved declarations.
- `PrimeFactorUnimodality/` — proof development.
- `PrimeFactorUnimodality/Mathlib/` — project-independent, Mathlib-oriented
  candidate modules behind a mechanically enforced one-way import boundary.
- `MATHLIB_PORTING.md` — proposed upstream paths and readiness for reusable
  candidate modules.
- `SIBLING_CAPABILITIES.md` — declaration-level index of reusable results in
  known sibling formalizations and the exact revisions reviewed.
- `comparator.json` — exact Challenge/Solution declarations and axiom boundary.
- `formalization.yaml` — Palomar/community metadata, sources, fidelity, and
  review disclosure.
- `paper/` — public research paper source.
- `scripts/` — reproducible build, lint, experiment, certificate, and Palomar
  verification tools.
- `data/` — only reasonably sized data that is relevant and reproducible.

Local research context and AI working files are intentionally ignored and never
part of the public repository history.

## Reuse before reproof

Before developing a general result that is absent from the pinned Mathlib,
consult [`SIBLING_CAPABILITIES.md`](SIBLING_CAPABILITIES.md). It distinguishes
complete headline theorems from independently proved leaves in active projects
and names stable modules or declarations to inspect. Borrow only from an exact
published commit after checking its licence, hypotheses, imports, placeholders,
axiom surface, and toolchain; then record the source and attribution locally.

## Build and checks

Install Git, Python 3.11+, Ruby, and `elan`, then run:

```text
python scripts/check.py --profile research
```

That checks the public-file boundary, Lean source policy, Python formatting,
lint, strict typing, tests, Palomar metadata mode, Mathlib-candidate isolation,
and the Lean build.

Before release, run:

```text
python scripts/check.py --profile release
./scripts/verify-comparator.sh
```

The Comparator command requires a supported Linux host with Git, Go, Ruby,
Rust/Cargo, Python, and Landrun. GitHub CI runs the pinned verifier stack.
It pins the matching upstream `leanprover/lean4export` v4.34.0 source and
compiles that source unchanged with the generated repository's exact Lean
v4.34.0 toolchain via `ELAN_TOOLCHAIN`. This keeps the exporter aligned with
the repository's `.olean` format without a fork or machine-local patch.

## Releases

`RELEASE_VERSION` contains the semantic version for the next completed
release. CI checks its format and tag collision before the long Lean build.
Research-mode repositories containing `TEMPLATE:` metadata never publish a
release. Once the real metadata and theorem surface are complete, a successful
`main` run publishes exactly three assets after every gate passes: the paper
PDF, a Linux `.lake/build` archive with project licensing, and an offline API
documentation ZIP with Lean and pinned-dependency notices. Reruns verify an
existing release at the same commit instead of duplicating it.

## Paper

The paper should state the exact mathematical result, its significance, source
relationship, proof architecture, formalization trust boundary, computation or
certificate coverage, limitations, automation disclosure, and actual review
status. Every theorem presented as proved must map to a kernel-checked Lean
declaration.

Its project-authored source and rendered PDF are dual-licensed under
Apache-2.0 or CC-BY-4.0, at the recipient's option. The repository's default
metadata licence remains Apache-2.0.

## Palomar

Development may begin in this public repository so GitHub CI is available from
the outset. Submit only after the full release profile passes at a clean commit,
that exact 40-character SHA is pushed, and the current
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
has been reviewed. Use the
[Palomar submission form](https://submit.palomar-registry.org/) only for the
verified commit.

A successful Lean build, Comparator check, NanoDa replay, or automated review
does not by itself establish novelty, source fidelity, mathematical
significance, or independent expert review.

## Licence

The repository's original material is licensed under
[Apache License 2.0](LICENSE) by default. The research paper is additionally
available under CC-BY-4.0, at the recipient's option. Mathematical provenance,
cited papers, supplied literature, dependencies, and generated archives are
covered by [LICENSING.md](LICENSING.md); this project does not claim ownership
of mathematical results or relicense third-party material.
