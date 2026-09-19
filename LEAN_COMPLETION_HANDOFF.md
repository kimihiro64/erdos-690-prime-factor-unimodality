# Lean completion handoff

This file records the current implementation boundary for Luna or any later
agent.  The objective is the exact all-`k` theorem in `Challenge.lean` and
`Solution.lean`.  Do not weaken the statement, import an unproved replacement,
or close an obligation with `sorry`, `admit`, an axiom, or `native_decide`.

## Priority order

1. Finish and elaborate every non-certificate module.
2. Make the concrete analytic providers required by the all-`k` assembly.
3. Only then regenerate and replay expensive finite certificates.
4. Replace the two public placeholders after the internal universal theorem is
   closed and audit it with `#print axioms`.

Certificate jobs may run remotely while source work continues.  Local replay
success is useful only for finding errors; GitHub CI is the authoritative
large-memory replay environment.

## Non-certificate work still open

### Split the finite interval monolith

`Helpers/Analytic/FinitePrimeIntervalRows.lean` is about 16,500 lines and used
roughly 10 GiB during an incomplete local elaboration.  Preserve its public
declaration names, but split it into modules below the existing facade:

- `FinitePrimeIntervalRows/Core.lean`: row structures, covers, append lemmas,
  monotonicity, and generic real-interval conversion.
- `FinitePrimeIntervalRows/EndpointBounds.lean`: logarithm and exponential
  endpoint inequalities only.
- `FinitePrimeIntervalRows/DusartPrefixLow.lean`: rows and chains from 3,275
  through 23,158.
- `FinitePrimeIntervalRows/DusartPrefixHigh.lean`: rows and chains from 23,159
  through 89,693.
- `FinitePrimeIntervalRows/Assembly.lean`: append the two prefixes and export
  `HasDusartShortIntervalPrimeBelow 89693`.

The existing `FinitePrimeIntervalRows.lean` should become a small import
facade.  Compile each new module before importing it into the facade.  Do not
change theorem statements merely to make the split easier.

### Close the analytic provider

`Proof/CompleteClassification.lean` already contains the adapters and the
paper-facing `WangCrapisAnalyticInputs` boundary.  Avoid adding another provider
abstraction.  Supply concrete proofs for its four fields, reusing the existing
MediumPNT, Abel, theta-error, finite endpoint-row, and 89,693-prefix results.
The endpoint data may be generated, but the adapters and all unbounded
arguments are non-certificate work and come first.

The final internal theorem should have type `CompleteClassification`; only
then should `PrimeFactorUnimodality.completeClassification` in the two public
files be filled.

### Verify dependency cleanliness

Run `#print axioms MediumPNT` and then `#print axioms` on the final internal
classification theorem in CI.  The local package checkout contains deliberate
compatibility edits; never clean or overwrite `.lake/packages` to make an
update command succeed.

## Record-gap certificate redesign

The current `Generated/FullRecordGapOwners` forest contains 2,175 files and
about 303 MiB of repeated nested `by_cases` dispatch.  This is an encoding
problem, not an unavoidable proof-size requirement.  Replace it after the
non-certificate work is complete.

`Proof/LargeRange/RecordGapOwnerRows.lean` is the new stable boundary.  The
replacement generator should:

1. Emit compact bounded rows with a computable `owner : Nat →
   FullRecordGapOwner` instead of one proof branch per offset.
2. Prove each row's `valid` field once by bounded kernel computation or small
   reusable arithmetic lemmas.
3. Convert elementary rows with `FullRecordGapSubOwnerRow.toRow` and
   `FullRecordGapAddOwnerRow.toRow`.
4. Package the existing 171 shared Fermat replay rows directly as
   `FullRecordGapSubRow`/`FullRecordGapAddRow`; do not recreate 10,918 files or
   10,918 independent expensive replays.
5. Prove one small ordered cover and invoke `fullRecordGapSubBlock_of_rows` and
   `fullRecordGapAddBlock_of_rows`.
6. Switch `Generated/FullRecordGapOwners.lean` to the compact assembly only
   after the replacement exports the exact existing block theorem names.
7. Remove the old owner forest in a separate commit only after the compact
   replacement builds in CI, so rollback never loses certificate source.

A good first prototype is one 512-offset subtraction row containing all three
owner kinds.  Compare source size and elaboration memory against one existing
4,000-line part before regenerating the full range.  If a literal lookup table
reduces source size but makes kernel reduction quadratic, use a balanced array
or formula-based owner function; do not return to generated proof branches.

## CI staging

The workflow is intentionally disabled at the GitHub level until source work
is ready.  When re-enabled, the `Lean foundations` job should elaborate the
analytic and reusable row infrastructure first.  The full build remains the
expensive certificate phase and must depend on that job.  Run large targets
one at a time if memory pressure appears; preserve `.lake` caches between
diagnostic runs.

The repository's tracked source is currently about 605 MiB uncompressed and
about 165 MiB in Git's packed object database.  Nearly all of the size is the
generated certificate source above.  The public-boundary limit is now 1 GiB;
that change does not remove or rewrite any data.
