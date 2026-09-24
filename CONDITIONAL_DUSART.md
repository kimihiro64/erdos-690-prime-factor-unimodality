# The all-k theorem conditional on Dusart

`PrimeFactorUnimodality.completeClassification_assuming_dusart` proves the same
`CompleteClassification` proposition as Challenge, with three explicit inputs:

- `HasDusartPrimeCountingBounds`;
- `HasDusartThetaBounds`;
- `HasDusartShortIntervalPrime`.

These are theorem parameters, not new axioms. The conclusion still quantifies
over **every positive k**, with unimodality exactly when `k ≤ 3`. The finite
classification through 38,000 and the uniform infinite tail are connected by
the existing reduction. The finite-range certificates remain obligations to
replay, not additional assumptions.

This target does not import the unfinished Dusart providers or zero-verification
modules. It also avoids the retired full record-gap and record-prime-witness
families. The record-twin primality and short record-gap certificates remain in
its actual dependency closure. No claim of a successful full build is made by
adding this target: the dedicated CI must pass first.

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
the seed equalities: the full conditional target still requires both actual
seed chains. Their generated data and cached replay modules are unchanged.

The original three hypotheses are unchanged. Internally, the uniform tail now
uses only `theta(q) < 1.001 q` and the existing lower theta bound for `q ≥ 3501`.
The selected-prime and primorial inequalities retain their original constants
and the tail still starts at `k = 38001`. `HasDusartThetaBounds` implies this
weaker interface; it is not redefined to mean a weaker published theorem.

For the subsequent formalization stage, the log-square estimate
`|theta(x) - x| ≤ x / (5 log(x)^2)` for `x ≥ 3594641` supplies both of these
tail inequalities above that endpoint. Only the finite theta prefix
`3501 ≤ q < 3594641` is then needed separately. The alternative all-k reduction
`completeClassification_of_finite_prefix_and_logSquared` exposes this route
without requiring the stronger theta upper estimate into the trillions. Its
finite classification, prime-counting, short-interval, finite-theta-prefix and
log-square inputs are still explicit obligations. This improvement does not
prove the original stronger Dusart upper theorem or close the zero-verification
and log-square finite-band obligations.

`CompleteClassificationSquaredReduction` also composes the existing
prime-counting and short-interval adapters with this weaker theta interface.
Its `SquaredThetaFiniteInputs` lists the three bounded prefixes and both exact
Abel anchor comparisons at 3,594,641. Given those inputs and the finite
classification, the sole remaining unbounded analytic input is the shared
log-square theta-error ray. This is a reduction of the remaining obligations,
not a claim that their numerical certificates or the ray have been proved.

## Building and resuming

The **Conditional all-k proof** workflow is manually dispatched and independent
of `DUSART_CI_BUILDS`. The unconditional workflow remains paused. New commits
do not cancel a running conditional build; another dispatch queues behind it.

Preview the exact dependency plan without running Lean:

```sh
python3 -m scripts.conditional_dusart_ci --plan
```

After restoring/building prerequisites, the focused Lean target is:

```sh
lake build +PrimeFactorUnimodality.Proof.CompleteClassificationConditional
lake env lean test/lean/ConditionalDusart.lean
```

CI builds owned modules in topological order, foundations first, without
restricting Lean's thread count. It downloads Mathlib's cache and applies the
reviewed dependency compatibility patches. Each job has a six-hour hard limit;
the replay runner stops after its 280-minute budget, leaving time for cleanup.
Every active target is named, with a heartbeat every 30 seconds. The final check
requires both successful elaboration of the all-k regression statement and an
axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

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

Once Dusart is formalized, supplying its three proofs removes these hypotheses
without changing the all-k conclusion. The unconditional Challenge and Solution
are deliberately unchanged in the meantime.

## Gated release and subsequent proof stages

1. **Conditional release, only after the complete target passes.** Add a
   dedicated release job that generates a conditional paper and documentation,
   packages the full conditional `.olean` dependency closure with the pinned
   sources/toolchain and compatibility patches, and records the exact commit,
   theorem type, three hypotheses, axiom audit, and artifact checksums. The paper
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

The release workflow and paper generation are gated future work, not completed
features of the initial conditional replay workflow.
