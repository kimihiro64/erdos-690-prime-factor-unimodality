# The all-k theorem conditional on Dusart

The primary conditional theorem is
`PrimeFactorUnimodality.completeClassification_assuming_theta_error`. It proves
the same `CompleteClassification` proposition as Challenge from the single
explicit hypothesis `HasThetaLogSquaredError (1 / 5) 3594641`:

`|theta(x) - x| ≤ x / (5 log(x)^2)` for every real `x ≥ 3594641`.

The conditional CI and release target is exclusively
`CompleteClassificationSquaredConditional`. The older
`completeClassification_assuming_dusart` theorem remains available in source
with three explicit inputs, but has no separate CI build or release audit:

- `HasDusartPrimeCountingBounds`;
- `HasDusartThetaBounds`;
- `HasDusartShortIntervalPrime`.

These are theorem parameters, not new axioms. The conclusion still quantifies
over **every positive k**, with unimodality exactly when `k ≤ 3`. The finite
classification through 38,000 and the uniform infinite tail are connected by
the existing reduction. The finite certificates have passed local replay;
they are not additional assumptions.

This target does not import the unfinished Dusart providers or zero-verification
modules. It also avoids the retired full record-gap and record-prime-witness
families. The record-twin primality and short record-gap certificates remain in
its actual dependency closure. The complete primary target has built locally
through 5,291 jobs, including its all-k regression and standard-axiom audit.
A published release still requires the dedicated CI and artifact gates.

The 500,001-entry reciprocal-prime enumeration is also absent. The already
proved finite Abel-summation inequality, using the same prime-counting input,
closes the upper record range directly. For `k ≥ 10372` the endpoint error is
less than `1/50`; the logarithmic difference exceeds `10.60 - 2.58`, leaving a
shell greater than eight. Thus its gap multiplier gives `4753 * 8 = 38024`,
above `k - 1 ≤ 37999`. `RecordPrimeCountingReduction` checks this bridge in Lean;
the old reciprocal certificates are preserved but are not required by this
target.

The twin endpoint modules use `decide +kernel` for their ten bounded arithmetic
checks. This invokes Lean's kernel, not native evaluation. Profiling the former
`rfl` implementation located repeated large-integer evaluation in elaborator
definitional equality. With the final seed equalities supplied as explicit
diagnostic parameters, the unchanged upper and lower endpoint statements now
check in about 34 and 35 seconds respectively on the local two-core machine,
while the seed chains also run. All ten audits contain only the three standard
axioms. This validates the endpoint arithmetic and its algebraic assembly, not
the seed equalities. Both actual seed chains have subsequently passed as part
of the complete local conditional builds. Their generated data and cached
replay modules are preserved.

The original three hypotheses are unchanged. Internally, the uniform tail now
uses only `theta(q) < 1.001 q` and the existing lower theta bound for `q ≥ 3501`.
The selected-prime and primorial inequalities retain their original constants
and the tail still starts at `k = 38001`. `HasDusartThetaBounds` implies this
weaker interface; it is not redefined to mean a weaker published theorem.

The alternative route uses the log-square estimate
`|theta(x) - x| ≤ x / (5 log(x)^2)` for `x ≥ 3594641`. It supplies the necessary
tail inequalities above that endpoint without requiring the stronger theta
upper estimate into the trillions. The lower-level reduction
`completeClassification_of_finite_prefix_and_logSquared` retains explicit
component inputs; the assembled providers described below discharge its finite
analytic inputs. This improvement does not prove the original stronger Dusart
upper theorem or close the zero-verification and log-square finite-band obligations.

`CompleteClassificationSquaredReduction` composes the prime-counting and
short-interval adapters with this weaker theta interface. All three finite
analytic prefixes are supplied by checked compact rows; the former
`SquaredThetaFiniteInputs` parameter is removed entirely.
The exact count `pi(3594641) = 256357` is kernel-checked by one packed sieve;
the same log-square theta hypothesis and elementary logarithm bounds then
prove both Abel anchor comparisons. No additional theta-product certificate
or anchor assumption is needed. The count pilot, including saved proof output,
completed in 5.09 seconds on the local two-core machine. Given the finite
classification, the sole remaining input is the shared unbounded log-square
theta-error ray. That ray is not claimed to have been proved by this reduction.

`DusartPublishedPiPrefix` covers every real input through 3,594,641. It extends
the closed prefix through 1,000 by 2,093 half-open rows in nine serial batches.
Each row checks rational log margins and local prime-count increments against
one certified packed sieve. At a prime right endpoint, the preceding cell uses
`pi(right - 1)`; the next cell includes the jump. The generic Lean coverage
proof checks adjacency and includes the final required endpoint. There is no
external primality oracle, per-prime proof family or native evaluation.
`DusartPublishedPrimeCounting` therefore obtains the global prime-counting
bounds from the theta-error ray alone, deriving both anchors and supplying
the finite prefix internally.

`DusartPublishedShortPrefix` proves the complete short-interval statement for
every real input from 3,275 through 3,594,641. Its 2,022 compact rows use a
shared certified sieve and smooth-power logarithm bounds. Each prime covers
the half-open interval to its left; at that prime, the next row supplies a
strictly larger witness. Eight serial batches passed in 75.7 seconds combined.
The older low-range families remain available but are not imported by this
provider. `DusartPublishedShortInterval` then gives the global short-interval
theorem from the same unbounded theta-error ray, with no finite-prefix premise.

`DusartTailThetaPrefix` supplies the full integer prefix
`3501 ≤ q < 3594641` for the weaker tail theta interface. Its 9,765 transitions
in 26 serial batches retain exact prime counts and rational theta enclosures.
Generic Chebyshev increment bounds turn local sieve counts and smooth-power
logarithm witnesses into theta bounds. Every cell after the consumer threshold
checks strict margins; a trace cannot omit its final checkpoint or skip a cell
crossing the threshold. The seed at three follows from log two and log three.
Per-batch digests keep earlier source identities stable when later rows change.
The complete 26-batch replay took 700 seconds combined locally, and the final
provider and classification reduction compiled. This measures the finite
prefix only, not the remaining unbounded theorem or full conditional target.

`CompleteClassificationSquaredConditional` supplies the actual finite
classification, including the record-twin certificate, to the strengthened
reduction. Its theorem `completeClassification_assuming_theta_error` has exactly
one explicit analytic parameter and the unchanged all-k conclusion. This is
reusable proof work for the unconditional result, not a hypothesis asserting
the classification. The separate three-Dusart target retains its original
interface. Both full conditional targets have passed local twin replays and
final axiom audits; only the reduced target is selected for CI and release.
The current unconditional
`Solution.lean` still uses the older provider assembly; switching it to the
replacement is a remaining integration step, not an already completed build.

The Mertens and Dusart chains share the pinned Euler--Maclaurin implementation.
The former vendored copy is now a forwarding module: defining the same global
`B1` twice prevented the two proof chains from importing together. Its previous
proof body is identical to the locked dependency's implementation, which imports
only Mathlib's Abel summation module. `test/lean/FinalThetaIntegration.lean`
checks the actual composition of the existing Dusart ray reduction with the
classification reduction; no analytic hypothesis is added by this import repair.

## Building and resuming

The **Conditional all-k proof** workflow runs on pushes to `main`, pull requests, and manual
dispatches when the repository state variable `CONDITIONAL_CI_BUILDS` equals
`enabled`. An unset value or `paused` skips the gated Lean and release jobs;
the original lightweight checks still run. This is independent of
`DUSART_CI_BUILDS`, which remains paused for the unconditional proof. New commits
do not cancel a running conditional build. The checkpointed stages build the
single-theta target only, including its actual finite certificate closure.
Pull requests may read checkpoints but cannot publish checkpoints or releases.

The workflow mirrors every stage of the original CI except Comparator:
release-version validation, metadata/source boundary, licensing, Python,
sandbox policy, foundations, certificate prebuild, analytic-tail checks,
final build and Lean linting, docs, paper, submission-link checks, and release.
The shared checks are copied by `scripts/render_conditional_workflow.py`;
the canonical fast gate detects a stale generated workflow.

Foundations run first. The high-memory prebuild ends at the checkpoint unit
containing `RecordTwinClosed`; the final build supplies the remaining analytic
prefix certificates and classification. The parallel analytic-tail job checks
the already-built certificate-independent reduction. Stage artifacts and the
durable checkpoint store reuse completed work without changing unit keys.

Preview the exact dependency plan without running Lean:

```sh
python3 -m scripts.conditional_dusart_ci --plan
```

After restoring/building prerequisites, the focused Lean target is:

```sh
lake build +PrimeFactorUnimodality.Proof.CompleteClassificationSquaredConditional
lake env lean test/lean/ConditionalTheta.lean
```

CI builds owned modules in topological order, foundations first, without
restricting Lean's thread count. It downloads Mathlib's cache and applies the
reviewed dependency compatibility patches. Each job has a six-hour hard limit;
the replay runner stops after its 280-minute budget, leaving time for cleanup.
Every active target is named, with a heartbeat every 30 seconds. The final check
requires successful elaboration of the all-k regression and analytic-anchor
regressions, and an axiom audit allowing only `propext`, `Classical.choice`, and
`Quot.sound`. Its uploaded audit receipt records the exact commit, theorem type,
axiom report and content-addressed checkpoint keys.

Completed 16-module units are immediately uploaded as content-addressed assets
in the draft releases `conditional-proof-checkpoints-v1-foundations` and
`conditional-proof-checkpoints-v1-certificates`. These are build storage, **not
mathematical releases**. Keys include the exact transitive source, toolchain,
dependency lock, build configuration, compatibility patches, and platform.
Changes outside that closure, timestamps, and commit IDs do not invalidate a
unit. Bundles include Lake traces and C output as well as Lean artifacts;
restoration checks an exact path allowlist and every file digest. Lake rechecks
its normal dependency traces before reuse.

Re-dispatch after fixing a source error or reaching the budget. Earlier saved
units survive a later failure and do not rely on Actions cache retention. The
currently incomplete unit is not saved; runner loss before upload can lose
that unit. Asset deletion or loss of the hosting service is also not protected
against: this is checkpointing, not an absolute durability guarantee. An
incomplete run fails visibly and never reports the conditional proof as passed.

Once the theta-error ray is formalized, supplying its proof removes the last
hypothesis without changing the all-k conclusion. The unconditional Challenge and Solution
are deliberately unchanged in the meantime.

## Gated release and subsequent proof stages

The conditional paper is `paper/conditional-paper.tex`; the original
`paper/research-paper.tex` is unchanged. Its seven-page rendering includes a
version-specific Wang–Crapis comparison, formal interfaces, completed analytic
replacements, and measured versus projected resource costs. The compact
`paper/conditional-resources.json` records selected experimental evidence and
its limitations. Generation requires an exact-commit, exact-statement audit
receipt; PDF checks reject unresolved references and overflowing text.

The docs job selects the conditional import closure, reuses the original
offline-index and licensing preparation tools with a separate landing page,
and generates declaration metadata in dependency order. Core documentation
scans are serial too. An incremental database is saved on a best-effort basis
with Actions cache; unlike certificate checkpoints, that cache can be evicted.

The compiled release includes all imported non-core Lean artifacts, not only
owned project modules. Bounded archive parts avoid duplicating the compiled
tree in staging. A source snapshot, locked dependency and toolchain identity,
compatibility scripts, dependency notices, exact axiom/type audit, and SHA-256
manifests accompany the PDF and offline docs. Install the selected Lean
toolchain separately; its binaries are not included. Publication verifies
downloaded assets before completing a distinctly named
`v<VERSION>-conditional.<COMMIT>` prerelease. It never promotes that result as
an unconditional solution or claims Comparator/NanoDa checks were run.

1. **Conditional release, only after all its CI gates pass.** The
   dedicated release job generates a conditional paper and documentation,
   packages the full conditional `.olean` dependency closure with the pinned
   sources/toolchain and compatibility patches, and records the exact commit,
   theorem type, single theta hypothesis, axiom audit, and artifact checksums. The paper
   must state precisely what remains assumed. Its account of the Dusart work
   must distinguish measurements from runtime projections, describe the
   analytic and computational optimizations attempted, and identify why no
   complete feasible formalization path has yet been verified. This is an
   engineering/formalization limitation, not a claim that Dusart's published
   mathematical results are in doubt or impossible to formalize. No conditional
   artifact may be labelled as an unconditional solution or certification.
2. **Feasible computation-backed Dusart target.** Identify and prove the
   analytic reductions, then discharge the exact remaining finite obligations
   using a measured, resumable computation path. A kernel-checked `rfl` path is
   preferred where feasible. A separately identified `native_decide` target is
   permitted for this later stage, with its enlarged trust boundary disclosed
   and audited. Native evaluation is not a substitute for proving the analytic
   reductions, complete coverage, or certificate soundness. Keep it distinct
   from the current conditional target and its standard-axiom policy.
3. **Reduce the remaining computational and trust burden.** Investigate stronger
   analytic bounds and new certificate/proof techniques. Measure the entire
   end-to-end path before a large implementation effort; reductions in one
   component alone do not establish feasibility of the full Dusart proof.

These release stages are implemented but publication still requires their
actual successful CI execution; passing local component tests is not a release.
