## Submission type

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information

## Problem

- **Problem ID(s):** JSP-000562 / Erdős 690.
- **Original problem source and exact location:** [Erdős Problems, problem 690][erdos].
- **Current entry and proposed change:** the [catalog entry][catalog] records
  the problem as Solved, with Lean proof: No. I submit my formalization of the
  complete all-k classification for consideration, with the published Dusart
  theorem retained as an explicit analytic input. I request clarification of
  how the submission requirements apply to that input, as set out below.
- **Related issue:** [#16][prior-issue], recording earlier formalization evidence.
- **Related PRs and distinction:** [#745][prior-four] gives a k = 4 counterexample;
  [#1307][prior-plby] and [#4033][prior-plby-new] reference a
  [formal theorem covering the classification through k = 20][prior-source].
  This submission covers **every positive integer k**, following the complete
  Wang–Crapis argument rather than only the earlier Cambie range.
- **Mathematical publication:** Shouqiao Wang and Davide Crapis,
  [*A Complete Answer to Erdős Problem 690*, arXiv:2605.08542v1][wang],
  8 May 2026, Theorem 1.1 and Corollary 1.2, with the proof in Sections 3–6.

Cambie's earlier counterexamples already settled the original universal
unimodality question negatively. The stronger conclusion formalized here is the
complete classification of the parameters for which unimodality holds.

## Formal statement

- **Complete mathematical solution:** Wang–Crapis, [arXiv:2605.08542v1][wang],
  Theorem 1.1 and Corollary 1.2, building on
  [Cambie's density and initial-case results][cambie].
- **Mathematical review reference or current review status:** submitted for
  mathematical and statement-correspondence review against those publications.
- **Formal statement location:** [definitions and classification][definitions],
  [analytic hypothesis][hypothesis], and [target theorem][theorem], pinned to
  `42484c8ba3d0ae33e93cc20269e16a26ed6e83c8`.
- **Fully qualified target theorem:**
  `PrimeFactorUnimodality.completeClassification_assuming_theta_error`.
- **Statement origin:** an adaptation of Wang–Crapis v1, with the external
  analytic input specified below.
- **Correspondence to the original problem:** d_k(p) denotes the natural density
  of positive integers whose k-th smallest **distinct** prime divisor is p.
  Primes are indexed in increasing order. Unimodality means weak increase to
  a mode followed by weak decrease. The conclusion is

$$
\forall k\in\mathbb N,\quad k\geq1\ \Longrightarrow\
\bigl((d_k(p))_{p\text{ prime}}\text{ is unimodal}\ \Longleftrightarrow\ k\leq3\bigr).
$$

The Lean theorem has exactly one analytic parameter:

```text
PrimeFactorUnimodality.HasThetaLogSquaredError (1 / 5) 3594641 →
  PrimeFactorUnimodality.CompleteClassification
```

This parameter is the following published estimate of Dusart:

$$
\mathcal H:\quad\forall x\in\mathbb R,\quad
x\geq3{,}594{,}641\ \Longrightarrow\
|\vartheta(x)-x|\leq\frac{x}{5(\log x)^2},
\qquad \vartheta(x)=\sum_{p\leq x}\log p.
$$

Here log is the natural logarithm and the cutoff is inclusive. The source is
[Dusart, *Estimates of Some Functions Over Primes without R.H.*,
arXiv:1002.0442v1, Theorem 5.2][dusart]. The hypothesis is an explicit theorem
argument, not an added axiom. The rational density formula is connected to the
actual natural density by the separate source theorem
[`PrimeFactorUnimodality.hasNaturalDensity_primeFactorDensity`][density].

### Clarification concerning the published Dusart theorem

The [submission requirements][rules] exclude conditional arguments relying on
additional **unproved** assumptions. Dusart's result is mathematically proved:
it is an established external tool used to supply the prime-distribution bounds,
not a conjecture or an unresolved mathematical step in the classification.
All problem-specific classification arguments, including the adaptations below,
are established in Lean from that tool.

The obstacle to supplying its formal proof is the computational scale of
reproducing and checking the rigorous numerical certification, particularly
finite-height zeta-zero verification and completeness. It is not mathematical
doubt about Dusart's theorem or the absence of a proof of the all-k argument.
The formal theorem nevertheless retains this parameter explicitly.

**Please clarify whether the rule concerning unproved assumptions also excludes
using a published, proved auxiliary theorem in this manner, when the
problem-specific argument is formalized and the remaining obstacle is formal
computational verification of the external tool.** Can the contribution be
assessed with this precise dependency disclosed, or must the formal proof of
Dusart's estimate be included before acceptance?

## Proof submission

```json
[
  {
    "repository": "https://github.com/kimihiro64/erdos-690-prime-factor-unimodality",
    "branch": "main",
    "commit": "42484c8ba3d0ae33e93cc20269e16a26ed6e83c8"
  }
]
```

- **Proof file and theorem:**
  [`PrimeFactorUnimodality/Proof/CompleteClassificationSquaredConditional.lean`][theorem];
  `PrimeFactorUnimodality.completeClassification_assuming_theta_error`.
- **Exact source commit:** [42484c8ba3d0ae33e93cc20269e16a26ed6e83c8][commit].
- **Release:** [v0.1.0-conditional.42484c8ba3d0][release].
- **Research paper:** [*A conditional Lean formalization of Erdős Problem 690*][paper].
- **How the proof establishes the statement:** the [assembly][reduction] derives
  the required prime-counting, short-interval and tail-theta bounds from the
  single Dusart input. Bounded analytic prefixes and endpoint anchors are
  supplied by Lean proofs and certificates. The finite classification through
  k = 38,000 includes the actual record-twin primality certificates. A uniform
  Chinese-remainder construction supplies the argument for every k ≥ 38,001.
  `test/lean/ConditionalTheta.lean` checks the exact all-k implication.

Neither the finite classification, record-twin primality nor the infinite-tail
conclusion is assumed. The conditional theorem uses the substantive proof
components intended for the unconditional result; providing the analytic
parameter's formal proof removes that parameter without changing the conclusion.

### Adaptations and improvements

The symmetric-sum comparison and descent-before-ascent strategy follow
Wang–Crapis. The following changes reduce the analytic and computational burden
of formal verification. The comparison is with **version 1** of their paper.

| Component | Wang–Crapis v1 | This formalization |
| --- | --- | --- |
| Finite/tail split | Finite through 8,600,001; tail from 8,600,002 | Finite through 38,000; tail from 38,001, with a proved uniform margin |
| Large-gap input | Published prime gap of length 1,113,106 | A certified block of 4,751 consecutive composite integers suffices, without primality proofs for the megagap endpoints |
| Later tail interval | Average-gap argument in (4P, 8P] | Reproved constants for (4P, 9P], where P is the relevant primorial |
| Reciprocal estimates | Sharper reciprocal bounds and numerical constants | Finite Abel lower bounds and a proved ordinary Mertens upper bound suffice |
| Record twins | Published record-prime data | Both 71,298-digit twin-prime primality proofs are replayed in Lean |

Relative to earlier implementations of this project, the smaller composite block
reduces 10,918 exceptional Fermat checks to one. A prime-counting consequence
replaces 380 prime-witness modules for the count below 500,000, and an Abel
comparison removes a 500,001-entry reciprocal enumeration. The tail only needs
the coarser upper bound θ(q) < 1.001q on its domain, avoiding a separate proof
of the stronger global coefficient 1 + 1/36,260.

External scripts generate compact certificate rows; Lean assemblers verify their
arithmetic, coverage and endpoint conventions. These changes eliminate proof
obligations rather than assume that larger computations would succeed.
They improve the formalization's resource requirements without claiming a new
discovery of the mathematical classification.

### Completing the analytic input

Rigorous zero verification requires validated function values and root/sign
certificates together with a completeness argument, including truncation,
rounding and coverage bounds. A fast external numerical evaluation or a list
of approximate zeros does not supply those kernel-checked facts.

The [paper][paper] and [resource ledger][resources] describe the analytic
reductions, packed-sieve and combinatorial-counting experiments, and rejected
high-height evaluation layouts. For example, one screened dense convolution
layout required approximately 3.92 TB of input data before other costs.
Component timings are distinguished from full-path estimates.

We are actively working to remove the remaining formal parameter and clean up
the development: weakening the analytic input needed by the classification,
proving the corresponding reductions, and developing shared, compact numerical
certificates with a feasible end-to-end verification cost.

## Reproduction

- **Exact Lean version and toolchain path:** `leanprover/lean4:v4.34.0`, specified
  in [`lean-toolchain`][toolchain].
- **Pinned dependencies and manifest:** [`lake-manifest.json`][dependencies],
  including Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- **Build instructions at the selected commit:** [build/resume instructions][instructions]
  and [conditional workflow][workflow].
- **Setup, build and statement check:** in a checkout of the specified commit,
  with elan, Git and Python 3 available:

```bash
elan toolchain install leanprover/lean4:v4.34.0
lake exe cache get
python3 scripts/patch_pnt_compat.py
python3 scripts/patch_primecert_compat.py
lake build +PrimeFactorUnimodality.Proof.CompleteClassificationSquaredConditional
lake env lean test/lean/ConditionalTheta.lean
lake env lean test/lean/TailThetaBounds.lean
lake env lean test/lean/DusartPublishedAnchors.lean
```

Keep the locked dependency revisions. The compatibility scripts apply the
reviewed API ports used by CI. Compiled artifacts can be restored using the
release manifest's instructions; artifact reuse is distinct from a clean build.

- **Axiom audit:**

```bash
lake env lean --stdin <<'LEAN'
import PrimeFactorUnimodality.Proof.CompleteClassificationSquaredConditional
#check @PrimeFactorUnimodality.completeClassification_assuming_theta_error
#print axioms PrimeFactorUnimodality.completeClassification_assuming_theta_error
LEAN
```

The [published audit][audit] gives the displayed conditional theorem type and
the axiom dependencies `[propext, Classical.choice, Quot.sound]`. It reports no
`sorryAx` or project-local axiom; the proof does not use `native_decide`.

The natural-density identification bridge can be checked separately:

```bash
lake build +PrimeFactorUnimodality.Definitions.DivisibilityPredicate
lake env lean --stdin <<'LEAN'
import PrimeFactorUnimodality.Definitions.DivisibilityPredicate
#check @PrimeFactorUnimodality.hasNaturalDensity_primeFactorDensity
#print axioms PrimeFactorUnimodality.hasNaturalDensity_primeFactorDensity
LEAN
```

## Pre-submission Lean verification (optional)

- **Method/tool and version:** GitHub Actions conditional workflow, Lean 4.34.0,
  with the locked dependencies and exact theorem/axiom audit.
- **Checked repository and full commit SHA:**
  `kimihiro64/erdos-690-prime-factor-unimodality`,
  `42484c8ba3d0ae33e93cc20269e16a26ed6e83c8` on `main`.
- **Verification date and conclusion:** 25 September 2026;
  [conditional CI run 36087662063][ci] passed. The
  [conditional release][release] was published at 02:59:55 UTC.
- **Coverage and trust dependencies:** the audited theorem establishes the
  classification for every positive k from the one displayed Dusart premise,
  using the three standard Lean axioms. The premise is visible in its type.
  The separate density-identification module is not included in this release's
  compiled closure or audit; the reproduction commands above include its
  separate verification.
- **Evidence:** [source commit][commit], [release][release], [paper][paper],
  [theorem/axiom audit][audit], [release integrity manifest][release-manifest],
  and [compiled-closure manifest][build-manifest]. The release includes a source
  snapshot, ten compiled Lean archive parts and dependency notices.

## Attribution

- **Mathematical solver(s) and contribution:** **Stijn Cambie**, for the earlier
  density/unimodality results and initial cases; **Shouqiao Wang and Davide
  Crapis**, for the complete all-k classification; **Pierre Dusart**, for the
  established auxiliary prime-distribution estimate. Their publications are
  linked above.
- **Lean formalization author and contribution:** **Jonas Whidden (@kimihiro64)**,
  for this AI-assisted formalization, its adaptations and computational
  reductions. **Requested recipient for the formalization contribution:
  Jonas Whidden.**
- **Independent verifier(s):** none listed; the linked CI and audit provide
  the project's reproducibility evidence.
- **Public authorship evidence:** [project metadata][authorship] and
  [paper source][paper-source] identify Jonas Whidden. `kimihiro64` is the
  GitHub account name. Mathlib, LeanCert, PrimeCert and PrimeNumberTheoremAnd
  retain their separate authorship and licenses; see the
  [licensing statement][licensing] and release dependency notices.

## Submission checklist

- [ ] I changed only the relevant catalog's solver attribution, Lean proof information or supporting sources and supplied the applicable evidence.
- [x] The submitted result fully solves the original problem. Any submitted Lean proof is complete at the specified commit, with no `sorry`, `admit` or added unproved assumptions replacing proof steps.
- [x] For Lean: I have linked the complete mathematical solution and its proof or publication evidence provided earlier, or supplied them in this PR, and identified the mathematical solver and Lean formalization author separately.
- [x] For Lean: I am claiming my own contribution in the original personal or organization repository, with verifiable contribution evidence for an organization repository; the selected commit is in the named branch, and I supplied statement correspondence, reproduction commands and axiom audit results.
- [x] This PR contains no Lean source files, archives, binaries, vendored dependencies or private identity/contact/payment information.

The completeness attestation is subject to the clarification requested above
concerning the published Dusart theorem.

[rules]: https://github.com/TheJustinSunPrize/awards/blob/1d1db84a39201357236183f0bbd620e2b220747e/CONTRIBUTING.md#external-solver-and-lean-submissions
[catalog]: https://github.com/TheJustinSunPrize/awards/blob/1d1db84a39201357236183f0bbd620e2b220747e/problems/catalog-0501-0600.md#JSP-000562
[erdos]: https://www.erdosproblems.com/690
[wang]: https://arxiv.org/html/2605.08542v1
[cambie]: https://arxiv.org/abs/2501.10333v1
[dusart]: https://arxiv.org/pdf/1002.0442v1#page=4
[theorem]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/PrimeFactorUnimodality/Proof/CompleteClassificationSquaredConditional.lean#L18
[definitions]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/PrimeFactorUnimodality/Definitions/KthPrimeFactor.lean#L32
[hypothesis]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/PrimeFactorUnimodality/Helpers/Analytic/ThetaLogSquaredError.lean#L13
[density]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/PrimeFactorUnimodality/Definitions/DivisibilityPredicate.lean#L336
[reduction]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/PrimeFactorUnimodality/Proof/CompleteClassificationSquaredReduction.lean
[commit]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/commit/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8
[release]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/tag/v0.1.0-conditional.42484c8ba3d0
[ci]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/actions/runs/36087662063
[paper]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/download/v0.1.0-conditional.42484c8ba3d0/conditional-paper.pdf
[paper-source]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/paper/conditional-paper.tex
[resources]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/download/v0.1.0-conditional.42484c8ba3d0/conditional-resources.json
[audit]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/download/v0.1.0-conditional.42484c8ba3d0/conditional-audit.json
[release-manifest]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/download/v0.1.0-conditional.42484c8ba3d0/conditional-release-manifest.json
[build-manifest]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/download/v0.1.0-conditional.42484c8ba3d0/conditional-build-manifest.json
[toolchain]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/lean-toolchain
[dependencies]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/lake-manifest.json
[workflow]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/.github/workflows/conditional-dusart.yml
[instructions]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/CONDITIONAL_DUSART.md#building-and-resuming
[authorship]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/formalization.yaml#L16
[licensing]: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/blob/42484c8ba3d0ae33e93cc20269e16a26ed6e83c8/LICENSING.md
[prior-issue]: https://github.com/TheJustinSunPrize/awards/issues/16
[prior-four]: https://github.com/TheJustinSunPrize/awards/pull/745
[prior-plby]: https://github.com/TheJustinSunPrize/awards/pull/1307
[prior-plby-new]: https://github.com/TheJustinSunPrize/awards/pull/4033
[prior-source]: https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2159
