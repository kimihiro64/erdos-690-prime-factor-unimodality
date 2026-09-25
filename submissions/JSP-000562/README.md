# JSP-000562 / Erdős 690 submission package

Prepared for **Jonas Whidden** on 25 September 2026. Nothing has been submitted
to the prize repository by preparing these files.

## Eligibility clarification and submission route

The [contribution rules][rules] exclude conditional arguments relying on
additional unproved assumptions. **Dusart's estimate is mathematically proved**;
the missing component here is its formal verification, with a computational
barrier in reproducing the numerical certification. The draft asks whether the
rule also excludes this use of an established auxiliary theorem when all
problem-specific classification arguments are formalized from it. Do not
preempt the organizers' answer by declaring the contribution eligible or
ineligible. The reviewed catalog records JSP-000562 as **Solved**, with **Lean
proof: No** and **Eligible to claim: No**; those fields are not changed by this
clarification request.

[submission.md](submission.md) is a ready-to-review **feedback/question draft**,
with the mathematical scope, attribution, reproducibility information and pinned
evidence normally needed for a contribution PR. Its proposed title is:

> [Feedback] JSP-000562 / Erdős 690: eligibility clarification for all-k formalization using Dusart

If Jonas decides to send it now, use the repository's
[Feedback, suggestion or question form][feedback] and paste the draft into its
single text field. This asks how the completeness rule applies to an established
external mathematical tool; it is not an award claim, candidate registration,
priority reservation, or assertion of unconditional Lean completeness.

## Before a future formalization PR

1. Obtain clarification of whether the published Dusart theorem can be used
   with the disclosed formal trust boundary, or whether its formal proof is
   required before acceptance. Follow the organizers' answer and update the
   exact source/release evidence for any subsequent proof changes. Continue
   working to discharge the premise regardless of the eligibility decision.
2. Include the natural-density identification bridge in the verification record,
   not just the classification of the rational recurrence. The present release
   audit covers the latter; the draft identifies this distinction explicitly.
3. Recheck the prize rules, catalog and existing submissions. Follow the then-current
   PR template and edit only the permitted fields in
   `problems/catalog-0501-0600.md`. Keep proof sources and binary assets in the
   original proof repository, not the prize repository.
4. Identify **Jonas Whidden (@kimihiro64)** as the formalization contributor and
   proposed recipient for that role. Preserve Cambie's, Wang's, Crapis's,
   Dusart's and dependency authors' separate credits. No new discovery of the
   classification or first-formalization priority is claimed here.
5. After acceptance and merger of the contribution PR, Jonas can make his own
   formalization claim through the official claim form. Identity confirmation
   and any private delivery/payment information go through the official process,
   not this public package. No identity verification or award decision is claimed.

## Evidence checked for this draft

- Prize rules and catalog at revision
  `1d1db84a39201357236183f0bbd620e2b220747e`.
- Original proof repository `kimihiro64/erdos-690-prime-factor-unimodality`, branch
  `main`, containing commit `42484c8ba3d0ae33e93cc20269e16a26ed6e83c8`.
- Successful conditional CI run `36087662063`, at that exact commit.
- Published prerelease `v0.1.0-conditional.42484c8ba3d0`, dated
  `2026-09-25T02:59:55Z`, its theorem/axiom audit, compiled-module manifest and assets.
- Wang–Crapis v1 and the pinned released paper's comparison and resource discussion.
- Related prize PRs #745, #1307 and #4033, and Issue #16. The actual pinned
  `plby/lean-proofs` theorem referenced by #1307/#4033 is bounded by `k ≤ 20`;
  the distinction in the draft is based on its source, not its PR title.

These are source, public-CI and release-evidence checks, not a newly executed
clean Lean build, independent kernel replay, or organizer verification.
Unpublished working-tree improvements are not attributed to the pinned release.

[rules]: https://github.com/TheJustinSunPrize/awards/blob/1d1db84a39201357236183f0bbd620e2b220747e/CONTRIBUTING.md#external-solver-and-lean-submissions
[feedback]: https://github.com/TheJustinSunPrize/awards/issues/new?template=feedback.yml
