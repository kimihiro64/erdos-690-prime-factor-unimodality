# Erdos 690: Prime-Factor Density Unimodality

[![CI](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/actions/workflows/ci.yml/badge.svg)](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/actions/workflows/ci.yml)

An unconditional Lean 4 proof of the complete classification:
for every positive integer `k`, the density of the `k`th smallest distinct
prime divisor is unimodal precisely when `k <= 3`.

## The proved statement

`PrimeFactorUnimodality.completeClassification_elementary` proves
`CompleteClassification` without an analytic hypothesis. The submission entry
point [Solution.lean](Solution.lean) exports the same result as
`PrimeFactorUnimodality.completeClassification`:

```lean
forall k : Nat, 1 <= k ->
  Iff (IsUnimodal (primeFactorDensity k)) (k <= 3)
```

The exact rational finite-density recursion is identified with natural density
by `hasNaturalDensity_primeFactorDensity`. Primes are ordered increasingly,
prime factors are distinct, and unimodality allows weak inequalities on both
sides of a mode.

The final theorem and a separate transport to the Mathlib-only
[Challenge.lean](Challenge.lean) definitions have been checked with Lean 4.34.0.
Their axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
The intentional placeholder in Challenge is the statement to be compared;
Solution and its proof dependency closure contain the implemented proof.

## Elementary proof route

The proof keeps the descent-before-ascent strategy of Wang and Crapis and
replaces the sharp analytic premise with elementary estimates.

1. A finite coefficient theorem proves that a tilted Bernoulli mean greater
   than degree `r` forces the adjacent symmetric-sum ratio below the tilt.
2. Factorial bounds and a five-term Chebyshev combination give the theta
   bounds and the weighted Mertens error `-2 < E(x) < 1/5` for `x >= 1000`.
3. Abel summation, retaining the integral below the smoothing parameter,
   supplies the smoothed prime-sum lower bound. Ordinary reciprocal-sum bounds
   supply the later ascent.
4. The original proofs cover `k <= 48`. The original fixed gap and twin
   witnesses, with the new estimates, cover `49 <= k <= 38000`.
5. A symbolically selected primorial, the existing CRT composite block, and
   an average-gap argument on `(4P,400P]` cover every `k >= 38001`.
   The scalar inequalities hold on the entire real ray `r >= 38000`,
   proved by differentiation.

There is no Dusart, RH, finite-height zeta-zero, or prime-counting hypothesis
in the final theorem. The new route adds no prime/zero enumeration and no
enlarged finite certificate interval. The original fixed witnesses remain.

The earlier conditional proof and the unfinished work on sharper Dusart
providers are retained in focused historical modules; they are not the proof
used by Solution or the public library root.

See [the paper PDF](paper/research-paper.pdf) and its
[TeX source](paper/research-paper.tex) for the derivation and the mapping to
Lean declarations.

## Repository map

- `Challenge.lean`: Mathlib-only all-parameter statement.
- `Solution.lean`: unconditional implementation of that statement.
- `PrimeFactorUnimodality/Proof/CompleteClassificationElementary.lean`:
  the three-range assembly.
- `PrimeFactorUnimodality/Helpers/Analytic/`: elementary analytic estimates
  and the uniform scalar argument.
- `PrimeFactorUnimodality/Definitions/DivisibilityPredicate.lean`:
  identification with the natural density of the prime-factor predicate.
- `PrimeFactorUnimodality/Mathlib/` and `MATHLIB_PORTING.md`:
  reusable Mathlib-oriented candidates and their proposed upstream paths.
- `paper/research-paper.tex`: current unconditional paper.
- `paper/conditional-paper.tex`: historical conditional proof account.
- `formalization.yaml`: attribution, scope, provenance, and review disclosure.
- `scripts/` and `test/`: build, source-policy, and verification tools.

Local AI working notes are ignored and are not public proof artifacts.

## Build and audit

The project pins Lean `v4.34.0` and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Keep the revisions in `lake-manifest.json`.

With Git, Python 3.11+, Ruby, and elan installed:

```sh
elan toolchain install leanprover/lean4:v4.34.0
lake exe cache get
python3 scripts/patch_pnt_compat.py
python3 scripts/patch_primecert_compat.py
lake build +PrimeFactorUnimodality.Proof.CompleteClassificationElementary
lake build +PrimeFactorUnimodality +Challenge +Solution
lake env lean test/lean/UnconditionalClassification.lean
python3 scripts/check.py --profile fast
```

The fixed twin-prime certificates are substantial. Published compiled objects
may be reused only after checking their source revision, toolchain, archive
hashes, and object hashes. A cache restore is not a fresh certificate replay.

For the complete development and release verification:

```sh
python3 scripts/check.py --profile research
python3 scripts/check.py --profile release
./scripts/verify-comparator.sh
```

Comparator, independent NanoDa replay, and the release profile require their
documented Linux tool stack. Local Lean compilation and axiom inspection are
reported separately from those checks; neither substitutes for independent
mathematical review.

Pushes to main run the unconditional release pipeline without a repository
variable opt-in. The proof job restores source-bound checkpoints, builds only
the elementary public dependency closure plus Challenge and Solution, and
checks the unconditional theorem type, natural-density bridge, copied-Challenge
transport, and their axioms. Licensing, Python, Comparator, documentation,
paper, and submission-link checks remain required before publication.

Historical Dusart diagnostics require a manual dispatch with `legacy_dusart`
selected and `DUSART_CI_BUILDS=enabled`; they are outside the release dependency
graph. The separate conditional workflow is manual-only and retains its
`CONDITIONAL_CI_BUILDS` opt-in. Neither historical route runs on ordinary pushes.

## MathDB submission

MathDB problem [315817](https://mathdb.com/p/315817/erdos-problem-690-let-d-k-p-be-the-density-of-those-integers)
uses the official [E690 target](https://github.com/mathdb-lean/problems/blob/8418d8e7e69f8267fbdf2b57d0bcd8f07a8d2a5d/problems/formal-conjectures/315817/E690.lean).
Its question is whether *every* positive `k` gives unimodality. Its accepted
negative answer has the form `Submission.answer := False` and
`Submission.solution : Problem.Target Submission.answer`.

That target is weaker than the complete classification above and quantifies
over real-valued functions recording the actual natural densities. Its frozen
environment is Lean 4.34.1 / Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, with an import allowlist that
does not include this project. The complete standalone answer is
[submissions/mathdb/E690.lean](submissions/mathdb/E690.lean), with its exact
[environment and verification record](submissions/mathdb/environment.json).
It includes the CRT counting and natural-density proofs and the strict
`k=4` valley at primes 13, 17, and 19, with no project imports.

The exact submission source, followed by axiom inspection commands, passed
Lean 4.34.1 against the unchanged official target. Its solution, density
bridge, and counterexample depend only on `propext`, `Classical.choice`, and
`Quot.sound`. An external MathDB grader run is not claimed.

Paste the entire standalone file into MathDB's solution editor; its grader
supplies `FtpEvalBench.E690`. This file uses the separate frozen environment,
so build it there rather than with this repository's Lean 4.34.0 toolchain.

## Attribution and review

Stijn Cambie proved the initial results and counterexamples. Shouqiao Wang and
Davide Crapis proposed the complete classification and its descent/ascent
strategy. Jonas Whidden is responsible for this AI-assisted Lean formalization
and its elementary adaptations. This repository claims a formalization and
proof adaptation, not priority for the mathematical classification.
See the paper and metadata for the sources and exact scope.

Independent expert review and an independent replay of the updated complete
proof are not claimed. Earlier conditional release audits apply only to the
commits they name.

## Reuse, submissions, and licensing

Before importing work from a sibling formalization, consult
[SIBLING_CAPABILITIES.md](SIBLING_CAPABILITIES.md) and verify its exact revision,
hypotheses, proof, toolchain, and licence. Import Mathlib candidates from their
focused modules or the optional `PrimeFactorUnimodality.Mathlib` facade.

For Palomar, review the current
[submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and use the [submission form](https://submit.palomar-registry.org/) only for an
exact pushed commit whose required release checks have passed.

Original repository material is licensed under [Apache-2.0](LICENSE).
The project-authored paper source and PDF are additionally available under
CC-BY-4.0, at the recipient's option. Third-party mathematical results,
software, certificates, and attribution retain their own provenance; see
[LICENSING.md](LICENSING.md).
