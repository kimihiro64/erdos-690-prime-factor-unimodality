# Record-gap certificates

The consumer declarations remain `fullRecordGapSubBlock` (1–455703) and
`fullRecordGapAddBlock` (1–657401). No mathematical statement is weakened.

## Diagnosis and replacement

The previous owner checker asked `decide` to evaluate `Nat.minFac` and
`padicValNat`. Their well-founded implementations do not reduce as that
certificate required. It also searched global lists repeatedly and generated
large case dispatchers. The previous modular-power path had the same reduction
problem and bundled all expensive witnesses into one job.

The replacement stores one divisor per offset, with zero marking an exception.
The kernel checks each positive divisor directly. Positional rows, their
lengths, and interval concatenation establish coverage without case trees.
The source archives are SHA-256 pinned; their residue logs select work but
are never accepted as proofs.

Exceptions use base-three Fermat tests. `PowModCheckpoint` proves the invariant
for structurally recursive binary windows. `replay_gap_fermat` proposes residues;
each 8192-bit window is checked by the kernel before its lemma is reused.
`PowModState` prevents definitional equality from attempting to evaluate the
astronomical *unreduced* power. Exponent bits are encoded as natural numbers,
not thousands of syntax nodes. There is no external truth oracle.

## Measurements and CI

On the development ARM machine, a 4096-offset owner row compiled in 9 seconds.
A real 18,601-digit exception, center minus 12, compiled in approximately
81 seconds. Its final module artifacts occupy about 130 KB, versus 2.7 MB for
the earlier checkpoint prototype. Its axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. These are representative measurements,
not a completed full-family benchmark.

There are 273 data rows and 273 replay rows, plus nine small assemblers.
CI uses 181 independent runner jobs, each with at most two sequential rows
and at most 100 Fermat exceptions. At the measured rate that is at most
135 minutes per job; runner performance varies. Replay steps stop at 150 minutes,
leaving 30 minutes of the 180-minute job budget to save completed artifacts even
after a step times out.
The entire computation is still approximately 200–250 serial runner-hours
(roughly 380 CPU-hours at the measured CPU utilization). Splitting
does not eliminate that work: it bounds each job and permits reuse.

Imports serialize the factor chain and each replay shard. No Lean thread-count
restriction is used. Each target reports its name, elapsed time, and process
memory every 30 seconds. Completed rows are cached even when a later row fails.
Cache keys include the toolchain, dependency manifest, checker, and row sources;
unrelated proof edits do not invalidate them. GitHub may evict caches, so cache
reuse is not guaranteed. Successful artifacts are retained seven days and
merged before final assembly. A missing-artifact guard prevents the final job
from silently starting all expensive replays in parallel.

## Regeneration and checks

Run `python scripts/render_full_record_gap_compact.py
PrimeFactorUnimodality/Proof/LargeRange/Generated/FullRecordGapCompact.lean`
(as one command). Downloaded archives stay in ignored `.research/`.
`--sample` generates only the first row for focused diagnostics.

The Python tests check every generated row against its renderer, exact domain
coverage, exception counts, semantic digest, shard budgets, and serial imports.
The pre-commit hook runs the fast source checks, both Ruff checks, mypy, and
pytest, matching the prebuild checks in CI. The compact family has an enforced
source-line ceiling.
