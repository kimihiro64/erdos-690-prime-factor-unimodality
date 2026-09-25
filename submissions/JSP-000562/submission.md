## Submission type

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information

Draft for Jonas Whidden's review, following the repository's [PR template][template].
Nothing has been submitted. The formal statement below includes a request for
clarification about the retained, mathematically established Dusart theorem.

I am **Jonas Whidden (@kimihiro64)**, the formalization contributor and proposed
recipient for the **Lean formalization** role, should the completed work become
eligible and be accepted. The development is AI-assisted; the mathematical
classification is credited to its original authors, not claimed as my discovery.

I have published a Lean 4 formalization of the **entire parameter classification**
for Erdős Problem 690: for every positive integer k, the density sequence for the
k-th smallest distinct prime divisor is unimodal exactly when k is at most three.
This is adapted from Wang–Crapis's complete argument, not restricted to the earlier
Cambie range through k = 20. **The released classification theorem is conditional
on one explicitly stated Dusart estimate.** Its conditional pipeline has passed
and the source, paper, compiled proof artifacts and axiom audit are public.

## Problem

- **Problem ID(s):** [JSP-000562][catalog] / Erdős 690.
- **Original problem source and exact location:** [Erdős Problems, problem 690][erdos].
- **Current entry and proposed change:** the catalog records Solved, Lean proof:
  No, and Eligible to claim: No. Proposed for review: reference Jonas Whidden's
  complete all-k formalization and the Wang–Crapis mathematical solution, with
  the retained Dusart premise disclosed. Seek the clarification below before
  asserting that Lean proof should be Yes. No catalog diff or status change is
  made by this review draft.
- **Related issue, if any:** no issue for this contribution has been opened;
  [Issue #16][prior-issue] records earlier formalization evidence.
- **Related PRs and how this contribution differs:** [#745][prior-four] describes
  a k = 4 counterexample; [#1307][prior-plby] and [#4033][prior-plby-new] cite a
  [theorem restricted to k ≤ 20][prior-source]. Our classification covers every
  positive k, while explicitly retaining the established analytic premise.
- **For solver/publication updates — complete mathematical solution:** Shouqiao Wang and Davide Crapis,
  [*A Complete Answer to Erdős Problem 690*, arXiv:2605.08542v1][wang],
  8 May 2026, Theorem 1.1 and Corollary 1.2; Sections 4–6 provide the analytic,
  finite-certificate and uniform-tail argument adapted here.
- **Earlier work:** Stijn Cambie,
  [*Resolution of Erdős' problems about unimodularity*, arXiv:2501.10333v1][cambie],
  2025, establishes the positive cases k = 1, 2, 3 and non-unimodality for
  4 ≤ k ≤ 20. Those counterexamples already answer the original universal
  unimodality question negatively; the further all-k classification is the
  stronger scope emphasized here.
- **Analytic input:** Pierre Dusart,
  [*Estimates of Some Functions Over Primes without R.H.*, arXiv:1002.0442v1][dusart],
  Theorem 5.2, the coefficient 0.2 with two logarithmic powers and cutoff 3,594,641.

The published mathematical solution is supplied as the source for review.
No prize-organizer mathematical review, independent verification, or endorsement
by any cited author is asserted.

## Formal statement

- **Complete mathematical solution (provided earlier or in this PR):**
  Wang–Crapis, [arXiv:2605.08542v1][wang], Theorem 1.1 and Corollary 1.2,
  with the detailed source and date under Problem above.
- **Mathematical review reference or current review status:** published solution
  supplied for review; no prize-organizer review is claimed.
- **Formal statement location, pinned to a full commit SHA:**
  [classification and definitions][definitions], [theta premise][hypothesis],
  and [conditional theorem][theorem], all at
  `42484c8ba3d0ae33e93cc20269e16a26ed6e83c8`.
- **Fully qualified target theorem name:**
  `PrimeFactorUnimodality.completeClassification_assuming_theta_error`.
- **Statement origin:** proposed statement requiring review, adapted from
  Wang–Crapis v1, with the disclosed Dusart premise; not a maintainer-approved
  unconditional statement.
- **Correspondence to the original problem:** the definitions, quantifiers,
  complete all-k conclusion, retained hypothesis and separate density bridge
  are specified below.

### Exact correspondence and trust boundary

Let d_k(p) be the natural density of positive integers whose k-th smallest
**distinct** prime divisor is p. Primes are ordered increasingly. Unimodality
means weak increase up to a mode followed by weak decrease. The conclusion covers
every k ≥ 1, with no upper bound:

$$
\forall k\in\mathbb N,\quad k\geq1\ \Longrightarrow\
\bigl((d_k(p))_{p\text{ prime}}\text{ is unimodal}\ \Longleftrightarrow\ k\leq3\bigr).
$$

The **single additional mathematical premise** is

$$
\mathcal H:\quad \forall x\in\mathbb R,\quad
x\geq3{,}594{,}641\ \Longrightarrow\
|\vartheta(x)-x|\leq\frac{x}{5(\log x)^2},
\qquad \vartheta(x)=\sum_{p\leq x}\log p.
$$

The cutoff is inclusive, x is real, and log is the natural logarithm.
The [released entry point][theorem] is
`PrimeFactorUnimodality.completeClassification_assuming_theta_error`, with the
audited type:

```text
PrimeFactorUnimodality.HasThetaLogSquaredError (1 / 5) 3594641 →
  PrimeFactorUnimodality.CompleteClassification
```

[CompleteClassification and the underlying definitions][definitions] specify
`∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3)`.
The [hypothesis definition][hypothesis] exposes the entire unbounded theta ray.
It is a theorem argument, **not a new axiom hidden in the environment**.

The natural-density interpretation has a separate, unconditional source theorem,
[`PrimeFactorUnimodality.hasNaturalDensity_primeFactorDensity`][density]. It
identifies the rational recurrence with the actual density of the prime-divisor
predicate, rather than assuming an independence model. Verification scope matters:
the released classification's audit is not an audit of this separate bridge, and
`Definitions.DivisibilityPredicate` is not listed in this release's bundled
compiled closure. The reproduction instructions below include checking it
separately; I do not claim that the conditional CI audited a combined
density-and-classification theorem.

### Clarification requested: established auxiliary theorem

I would like clarification of how the [contribution rules][rules] apply to this
specific situation. Their exclusion concerns conditional arguments relying on
additional **unproved** assumptions. Dusart's estimate is a published, proved
theorem used as an external analytic tool, not a conjecture or a new mathematical
step left unjustified in the solution of Erdős 690. The problem-specific
classification arguments, including the adaptations described below, are
established in Lean from that estimate; they are not themselves assumed.

**Does the exclusion also apply when the sole retained premise is an established
auxiliary theorem whose numerical certification presents a computational wall
for formal verification, rather than an unresolved mathematical claim?** Must a
formal proof of Dusart's estimate be included in the Lean dependency closure
before this contribution can be accepted, or can the prize assess the complete
problem-specific formalization with that published tool and its precise trust
boundary explicitly disclosed?

The reason for retaining this premise is the scale of the rigorous computation
behind its verification, especially the zero-verification work, not doubt about
the truth of Dusart's result or a missing mathematical idea in the all-k
classification. We are continuing work to remove that computational barrier.
We are not asserting that the current release is an unconditional kernel proof,
nor presuming either eligibility or ineligibility. Please clarify the applicable
standard and submission route. No catalog status change, priority reservation,
or start of an award-review period is presumed by this request.

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

- **Proof file at the selected commit and fully qualified theorem name:**
  [`PrimeFactorUnimodality/Proof/CompleteClassificationSquaredConditional.lean`][theorem];
  `PrimeFactorUnimodality.completeClassification_assuming_theta_error`.
- **How the proof establishes the formal statement above, including any separate
  verification entry:** the assembly below uses the actual finite proof and
  infinite-tail argument. `test/lean/ConditionalTheta.lean` checks the exact
  all-k implication. The separate natural-density bridge and audit limitation
  are disclosed under Formal statement and Reproduction.

### What is proved, rather than assumed

The [assembly][reduction] derives the needed prime-counting, short-interval and
tail-theta interfaces from the one premise. The bounded analytic prefixes and
endpoint anchors are discharged by Lean proofs and certificates. The finite
classification through k = 38,000 includes the actual record-twin primality
certificates. For every k ≥ 38,001, the proof uses a uniform Chinese-remainder
construction and a later ascent to exclude unimodality.

Thus the conditional target does **not** assume its finite classification,
record-twin primality, an arbitrary-k tail conclusion, or three separate
unproved analytic providers. It composes the substantive proof components that
will also be used in the unconditional result. Supplying a proof of the displayed
theta hypothesis removes that parameter without changing the all-k conclusion.

### Differences and improvements over Wang–Crapis v1

The core first-difference/symmetric-sum mechanism and descent-before-ascent
strategy are retained. The [released paper][paper], especially its comparison
section, explains the following changes and their Lean implementations.

| Component | Wang–Crapis v1 | This formalization |
| --- | --- | --- |
| Finite range and uniform tail | Finite through 8,600,001; tail from 8,600,002 | Finite through 38,000; tail from 38,001, with a proved uniform margin |
| Large-gap input | Published gap of length 1,113,106 | A certified block of 4,751 consecutive composite integers suffices; primality of the megagap endpoints is unnecessary |
| Later tail interval | Average-gap argument in (4P, 8P] | Reproved constants for (4P, 9P], with P the relevant primorial |
| Reciprocal-prime estimates | Sharper estimates and numerical constants | A finite Abel lower bound and a proved ordinary Mertens upper bound suffice; the published decimal enclosures are not required |
| Record-twin input | Published record-prime data | Both 71,298-digit twin-prime primality proofs are replayed in Lean |

There are also concrete improvements over earlier designs of this project:

- The reduced composite block needs one exceptional Fermat check instead of
  10,918 in the retired full-gap representation.
- A prime-counting consequence replaces the former 380 prime-witness modules
  for the bound of at least 38,000 primes below 500,000.
- An Abel comparison removes the former 500,001-entry reciprocal enumeration.
- The tail only requires the coarser upper bound θ(q) < 1.001q on its domain,
  not a separate formalization of the stronger global coefficient 1 + 1/36,260.
- External scripts generate compact rows; proved Lean assemblers check their
  arithmetic, endpoint conventions and coverage. Resumable, content-addressed
  artifacts preserve expensive completed work across unrelated source changes.

These are reductions of the formal proof's analytic and computational burden,
not a new discovery of the classification or a claim to stronger prime bounds.
In particular, the complete mathematical theorem of Wang–Crapis is unconditional;
the present formal theorem has the explicit hypothesis described above.

### Why the result remains conditional, and ongoing work

Dusart's estimate is a published theorem, not an additional conjecture or an
assumption of the full Riemann hypothesis. There is no claim here of mathematical
uncertainty about that result. It supplies an external analytic tool; all
problem-specific deductions from it are established in the conditional
classification. The outstanding task is reproducing the tool's proof and
numerical certification within Lean's trust boundary, not finding a new
mathematical proof of the classification. The main barrier in the approaches
investigated is the sheer scale of
rigorous finite-height verification of zeta zeros **including completeness**,
together with the analytic error bounds and finite prime/theta data linking that
verification to the displayed estimate.

A list of approximate zeros is not enough. The formal route must validate
function enclosures and signs or root brackets, control truncation and rounding,
and certify that no zeros in the required region were missed. Fast external
numerical evaluations do not by themselves establish those facts in Lean.
Zero verification is part of the methods investigated, not an assertion that
every possible proof of the theta estimate must follow that route.

The [paper][paper] and [resource ledger][resources] separate measurements from
projections. For example, the approximately ten-day combinatorial-counting
scenario concerned only one finite-counting component, not a complete Dusart
proof. A screened high-height convolution layout required about 3.92 TB of dense
input data before other costs and was rejected. Analytic height reductions,
packed sieves and shared transforms improve individual components, but a feasible
end-to-end formal zero-verification route has not yet been demonstrated.

We are **actively working to make the result unconditional and to clean up the
formalization**: weakening the analytic input actually needed by the consumers,
proving more of the analytic reductions, developing smaller/shared certificate
representations, and measuring complete numerical-checking paths before large
runs. These are ongoing efforts, not completed results attributed to this
release. There is no claim that Dusart is impossible to formalize, or that a
passing conditional build has discharged its hypothesis.

## Reproduction

- **Exact Lean version and `lean-toolchain` path:** `leanprover/lean4:v4.34.0`,
  recorded in [`lean-toolchain`][toolchain].
- **Pinned dependencies and manifest path:** [`lake-manifest.json`][dependencies];
  Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, with all other revisions
  recorded there. Do not replace the pins with `lake update`.
- **Build instructions pinned to the selected commit:** [build/resume guide][instructions]
  and [conditional CI workflow][workflow].
- **Commands for setup, clean build and checking each target theorem:** below;
  the exact-statement regression is `test/lean/ConditionalTheta.lean`.
- **Axiom audit command and output for each target:** the commands below include
  `#print axioms PrimeFactorUnimodality.completeClassification_assuming_theta_error`.
  Its [published audit][audit] reports `[propext, Classical.choice, Quot.sound]`.
  The separate density-bridge commands are additional reviewer checks, not an
  already published audit of that bridge.

With elan, Git and Python 3 available, in a checkout of that commit:

```bash
set -euo pipefail
test "$(git rev-parse HEAD)" = 42484c8ba3d0ae33e93cc20269e16a26ed6e83c8
elan toolchain install leanprover/lean4:v4.34.0
lake exe cache get
python3 scripts/patch_pnt_compat.py
python3 scripts/patch_primecert_compat.py
lake build +PrimeFactorUnimodality.Proof.CompleteClassificationSquaredConditional
lake env lean test/lean/ConditionalTheta.lean
lake env lean test/lean/TailThetaBounds.lean
lake env lean test/lean/DusartPublishedAnchors.lean
```

The two compatibility scripts are reviewed API ports at pinned dependency
revisions, not theorem assumptions. For resource-bounded checkpointed builds,
see the [exact CI workflow][workflow] and [build/resume instructions][instructions].
For artifact reuse, follow the compiled manifest's instructions: install the
same toolchain, obtain the locked dependency sources, apply the compatibility
ports, verify archive digests, and extract all ten compiled parts at the project
root. A warm reuse check is not a fresh compilation of every proof.

To inspect the actual statement and its axiom dependencies, and separately check
the density-identification bridge:

```bash
lake build +PrimeFactorUnimodality.Definitions.DivisibilityPredicate
lake env lean --stdin <<'LEAN'
import PrimeFactorUnimodality.Proof.CompleteClassificationSquaredConditional
import PrimeFactorUnimodality.Definitions.DivisibilityPredicate
#check @PrimeFactorUnimodality.completeClassification_assuming_theta_error
#print axioms PrimeFactorUnimodality.completeClassification_assuming_theta_error
#check @PrimeFactorUnimodality.hasNaturalDensity_primeFactorDensity
#print axioms PrimeFactorUnimodality.hasNaturalDensity_primeFactorDensity
LEAN
```

The CI and published audit establish the named conditional classification check;
the extra density-bridge commands are supplied for reviewer reproduction, not
reported here as a new completed audit. The unconditional `Solution.lean` is not
the target certified by this prerelease.

## Pre-submission Lean verification (optional)

- **Method/tool and version, if available:** project GitHub Actions conditional
  workflow, Lean 4.34.0 and pinned dependencies; source and release-evidence
  inspection. No execution of the optional `lean-verify` skill is claimed.
- **Checked repository and full commit SHA:** original repository
  `kimihiro64/erdos-690-prime-factor-unimodality`,
  `42484c8ba3d0ae33e93cc20269e16a26ed6e83c8` on `main`. The separate
  `review/jsp-000562` branch contains correspondence only, not a changed proof.
- **Verification date, actual conclusion and limitations:** 25 September 2026;
  conditional classification CI passed and its release was published. This
  does not discharge the theta premise or establish prize eligibility.
- **Summary of statement correspondence, coverage, Lean checks and trust
  dependencies:** every positive k is covered with one explicit Dusart premise;
  the final theorem uses only the three standard Lean axioms. The separate
  density bridge is outside the published audit/bundle. No independent human
  or Comparator/NanoDa verification is asserted.
- **External report/log/evidence links:** exact source [commit][commit],
  [successful CI run 36087662063][ci], [published release][release],
  [research paper][paper] and [source][paper-source], [theorem/axiom audit][audit],
  [release SHA-256 manifest][release-manifest] and [compiled-closure manifest][build-manifest].

The commit was verified to be contained in `main` when preparing this draft.
The conditional prerelease was published at **2026-09-25 02:59:55 UTC**.
It contains the source snapshot, ten compiled Lean archive parts and dependency
notices. These remain in the proof repository, not the prize repository.

There is no `sorryAx` or project-local axiom in the target's reported axiom
dependencies, and its proof does not use `native_decide`. A standard-axiom audit
does not make the implication unconditional. API documentation is not included
and Lean lint cleanup is deferred; no unconditional Challenge/Solution release
gate is claimed to have passed.

The downloaded audit's SHA-256 is
`e9435f5767018e20b299f83300dc8ce1cd063de8f8950f96ca16eaaa3edff258`;
the release-manifest SHA-256 is
`ccc1d83721ec44efd6a686dd4ba6379485e684d8ea0bc0b300d5819abdacb05b`.

## Attribution

- **Mathematical solver(s) and contribution:** Stijn Cambie for the initial
  density/unimodality results; Shouqiao Wang and Davide Crapis for the complete
  all-k classification; Pierre Dusart for the auxiliary analytic estimate.
- **Lean formalization author(s) and contribution:** Jonas Whidden
  (@kimihiro64), for this AI-assisted formalization and its documented adaptations.
- **Independent verifier(s), if any:** none claimed; project CI is not an
  independent human review or organizer acceptance.
- **Public authorship evidence:** [project authorship record][authorship] and
  [paper source][paper-source], with account/recipient attribution below.

**Formalization contributor and proposed formalization recipient: Jonas Whidden.**
`kimihiro64` is my GitHub account name, not the intended recipient name.
The [project authorship record][authorship] and [paper source][paper-source]
identify Jonas Whidden. Development and preparation of this draft used AI
assistance. Existing Mathlib, LeanCert, PrimeCert and PrimeNumberTheoremAnd
contributions retain their authorship and licenses; [licensing details][licensing]
and the release's dependency notices are provided. No sole authorship of those
dependencies is claimed.

Credit for the earlier density/unimodality work belongs to **Stijn Cambie**;
credit for the complete mathematical classification belongs to **Shouqiao Wang
and Davide Crapis**; the retained explicit analytic estimate is due to
**Pierre Dusart**. My proposed role is the formalization and its documented
adaptations, not a solver claim replacing those mathematical credits.

Related records checked on 25 September 2026 include [Issue #16][prior-issue],
[PR #745][prior-four], [PR #1307][prior-plby] and [PR #4033][prior-plby-new]. The
`plby/lean-proofs` version cited by the latter two proves the positive cases
and non-unimodality through k = 20, as shown by its [actual final theorem][prior-source].
PR #745 describes a k = 4 counterexample. This development has broader parameter
coverage, while also explicitly retaining the analytic condition; it does not
claim those earlier unconditional finite results are conditional. No first-proof
or award-priority claim is made, and no existing author's credit should be removed.

Any eventual award application would be made by Jonas Whidden for his own
formalization contribution, after the required acceptance and verification steps.
Identity confirmation, recipient approval and private payment/delivery details
remain subject to the prize's official process; none is asserted complete here.

## Submission checklist

- [ ] I changed only the relevant catalog's solver attribution, Lean proof information or supporting sources and supplied the applicable evidence.
- [ ] The submitted result fully solves the original problem. Any submitted Lean proof is complete at the specified commit, with no `sorry`, `admit` or added unproved assumptions replacing proof steps.
- [x] For Lean: I have linked the complete mathematical solution and its proof or publication evidence provided earlier, or supplied them in this PR, and identified the mathematical solver and Lean formalization author separately.
- [x] For Lean: I am claiming my own contribution in the original personal or organization repository, with verifiable contribution evidence for an organization repository; the selected commit is in the named branch, and I supplied statement correspondence, reproduction commands and axiom audit results.
- [x] This PR contains no Lean source files, archives, binaries, vendored dependencies or private identity/contact/payment information.

The first box is unchecked because this is a review draft, not a catalog PR.
The second is left unchecked pending clarification of how the completeness
requirement applies to the established Dusart theorem retained as an explicit
Lean parameter. Leaving it unchecked does not assert that Dusart is mathematically
unproved or that the organizers have decided eligibility.

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
[template]: https://github.com/TheJustinSunPrize/awards/blob/1d1db84a39201357236183f0bbd620e2b220747e/.github/PULL_REQUEST_TEMPLATE.md
