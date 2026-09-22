# Record-gap replacement and retained certificates

The classification no longer depends on the full 1,113,106-gap certificate or
its 10,918 large Fermat tests. A uniform CRT proof now starts at `k = 38001`
and joins the existing finite classification through `38000`. The exact
all-`k` statements in `Challenge.lean` and `Solution.lean` are unchanged.

## Analytic replacement

Write `S(X)` for the sum of `1/p` over primes at most `X`. For natural numbers
`600 <= X <= Y`, the existing prime-counting bounds imply

```text
S(Y) - S(X) >= log(log Y) - log(log X)
              - (6381/5000)/(log X)^2 - 1/X.
```

`PrimeReciprocalAbel.lean` proves the finite Abel identity, using Mathlib's
Abel summation theorem. `PrimeCountingReciprocalShell.lean` bounds the integral
and endpoints. Its floor correction is explicit: the natural prime-counting
lower bound gives `pi(floor t) >= t/log t + t/(log t)^2 - 1`, whose extra
integral cost is at most `1/X`. No sharp Mertens remainder is assumed.

Set `r = k - 1`, `X = primeAt(r - 1) - 1`, and `Y = primorial q` in the existing
CRT construction. `TailShellNumerics.lean` proves `X >= 10*r` and a uniform
positive descent margin for all `r >= 38000`. A tangent-line bound for the
logarithm gives positive rational intercept
`877288074251/1231383407380000` and slope `3078619/10355190`; this is not a
sampled numerical check. The ascent uses the existing ordinary Mertens upper
bound. `UniformTailClosedMertens.lean` assembles both inequalities.

`completeClassification_of_finite_prefix_and_primeCounting` is the focused
all-`k` reduction. `CompleteClassificationCore.lean` instantiates its finite
prefix and retains the existing provider adapters, including compatibility
names containing `full_record`. Those names no longer import `FullRecordRange`.

The replacement retains the prime-counting, theta, and short-interval/pair
assumptions. It does not prove the remaining Dusart providers. The existing
smaller 4,751-integer composite block (one Fermat exception) and record-twin
certificate also remain required.

## Verification and CI

The new analytic tail and focused classification reduction elaborate. Their
axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`. This
checks the replacement with its explicit inputs, not completion of the entire
public proof and all its finite/provider dependencies.

```sh
lake build +PrimeFactorUnimodality.Proof.CompleteClassificationReduction
python scripts/check_tail_replacement.py
python scripts/check.py --profile fast
```

CI's `analytic-tail` job checks the certificate-independent reduction and
passes its artifacts to the complete build. The old full-gap owner/replay
matrix is not scheduled. The fast boundary check traverses imports from
`Solution`, requires the analytic tail, and rejects the full-gap family.
Regression tests check this boundary, the rational margin, and the workflow.
The pre-commit hook also runs Ruff formatting and lint, mypy, and pytest.

## Preserved legacy sources

The full-gap generated rows, archive audit, replay scripts, and existing
caches are retained. No cached build files are deleted. The legacy consumers
`fullRecordGapSubBlock` (1–455703) and `fullRecordGapAddBlock` (1–657401) retain
their statements but are outside the required classification import chain.

The archived interior cover has 1,087,142 small-factor cases, 15,045 additional
published factors, and 10,918 Fermat exceptions. Archive hashes and residue
logs select witnesses; they are never accepted as proofs. The compact checker
uses positional divisor rows and reusable assembly. Fermat exceptions use
kernel-checked binary windows, not an external truth oracle.

The previous 200–250 serial runner-hour estimate described replaying that
entire legacy family, not the new analytic proof. The replacement removes
that work from the required proof rather than distributing it across runners.
The legacy renderer remains available for independent record-gap work:

```sh
python scripts/render_full_record_gap_compact.py \
  PrimeFactorUnimodality/Proof/LargeRange/Generated/FullRecordGapCompact.lean
```

Do not regenerate or replay it as a prerequisite for the all-`k` classification.
