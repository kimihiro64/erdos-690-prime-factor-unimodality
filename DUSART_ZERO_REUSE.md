# Reuse audit for the Dusart zero-sum layer

## Newest follow-up: analytic takeover at three billion (2026-09-23)

The elementary prime-power correction now costs `1.6 * sqrt(x)`, rather
than `6 * sqrt(x)`, for every real `x ≥ 3000000000`. The new candidate
`Chebyshev.PsiBounds` retains Mathlib's decreasing logarithmic error in
`psi_le`. `DusartSharperRootCorrection` applies it at the square and cube
roots, then uses Mathlib's Costa-Pereira three-root inequality. No finite
prime certificate or additional zero information is used for this improvement.
This sharpens the psi-to-theta transfer discussed in
[Dusart's paper, Section 3](https://arxiv.org/pdf/1002.0442), without assuming
the stronger numerical bounds stated there.

`DusartBillionCutoffTheta` proves the three complete intervals
`[3000000000, 3400000000]`, `[3400000000, 5000000000]`, and
`[5000000000, 10000000000]`, with both endpoints included. The existing
order-three psi estimate, both averages, smoothing loss and complete
infinite tails are unchanged. The resulting normalized upper budgets are
strictly below `1/5`, verified by exact rational arithmetic in Lean.
`DusartEarlierCutoff` joins this bridge to the existing infinite ray.
The finite-band, prime-trace and Turing/checkpoint consumers in
`DusartVerifiedBootstrap` now require data only through `3000000000`.
The conclusion is still `HasThetaLogSquaredError (1 / 5) 3594641`.

The endpoint reduction from ten to three billion removes 70% of the
numeric range, not necessarily 70% of certificate work. The same heuristic
mesh and 64-stratum operation model now estimates 23,179 checkpoints and
307,016,043 rows, versus 29,235 checkpoints and 799,223,045 rows. At the
measured small-prototype rate this is approximately 10.5 serial days,
down from 27.3. These are workload projections, not certified coverage or
end-to-end timings; shared-table, theta/log and zero verification costs
remain excluded. The existing row-by-row approach remains infeasible.
The finite-certificates design gate still prohibits producing a large
family until batched arithmetic and shared lookup verification are practical.

This does not discharge the low-zero data: the bridge still uses height
`25000000`, and the infinite ray still requires `1000000000`. Finite theta
coverage, shared count tables, anchors and the unconditional providers
remain open. A floating-point parameter scout suggests further possible
savings near 2.5 billion, but that smaller cutoff is not proved or used.
CI builds remain paused; the three new modules and their small regressions
are configured as sequential targets for when builds resume.

All five new or affected proof modules, both facades and nine Lean test
files compile. All 22 audited public theorem closures use only `propext`,
`Classical.choice` and `Quot.sound`. The canonical fast gate, Ruff
format/lint, mypy, 186 Python tests and actionlint pass.

## Previous follow-up: exact Meissel counting and external dependency rows (2026-09-23)

The new Mathlib candidates `PartialSieve`, `PartialSievePrimeLeaves`, and
`PrimeCountingMeissel` prove the exact combinatorial counting identity, not
an assumption that an external prime-counting program is correct. They
identify partial-sieve values with positive coprime-interval cardinalities,
prove one-prime removal and completeness of the canonical prime prefix,
and telescope removal between the cube-root and square-root cutoffs.
After the cube cutoff, the removed counts are prime counts at smaller
quotient endpoints. Both cutoff inequalities have their strict boundaries.
The argument is the classical Meissel decomposition described in
[Oliveira e Silva's combinatorial-method account](https://sweet.ua.pt/tos/bib/5.4.pdf),
proved here directly using Mathlib finite sets, coprimality and prime enumeration.

`PartialSieveRows` verifies external values and backward dependency indices
using local integer relations. It never recomputes the recursive partial
sieve in its Boolean checker. Previously certified leaves can be shared,
and independently checked index blocks can be joined. Every imported leaf
retains an actual validity proof. `MeisselRows` checks externally supplied
correction subtotals one addition at a time, and derives `Nat.primeCounting`
from these checks, a verified prime prefix, a verified partial-sieve claim,
and verified small quotient counts. Sparse primality evidence alone still
does not satisfy these complete-count premises.

`PartialSievePeriodic` supplies the shared-wheel leaf: a proved remainder
count plus the totient of one complete period determines the count at any
larger endpoint. It reuses the existing periodic-count candidate and
Mathlib's coprime-interval totient identity. A regression proves the number
of positive integers coprime to six through `10000000000` is `3333333333`
from the tiny remainder alone; this is a partial-sieve count, not a claim
about the number of primes at that endpoint.

These are non-certificate foundations, not a completed numerical provider.
The row feasibility probe remains below the required full-range throughput;
no large family is generated or claimed to run in minutes. The next
engineering gate is substantial batching/compression of the local checks
and certification of their shared small tables. The finite theta coverage,
high-height zero data, anchors, and unconditional all-k providers remain
open. CI builds remain paused. The new foundations and their small
regressions are configured as sequential CI targets for when builds resume.

All six new modules and both affected facades compile. Six Lean regression
files include an end-to-end Meissel proof of `primeCounting 100 = 25` and
rejection checks for false values, forward/cyclic dependencies, missing
leaves, and invalid cutoffs. All 24 audited theorem closures use only the
standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The 183
Python tests, canonical fast gate, Ruff format/lint, mypy, and actionlint pass.

## Previous follow-up: analytic takeover at ten billion (2026-09-23)

`DusartEarlierCutoffScalars`, `DusartEarlierCutoffBudget`, and
`DusartEarlierCutoffTheta` prove two complete analytic intervals:
`[10000000000, 100000000000]` and `[100000000000, 1441000000000]`.
They use the existing order-three psi formula with step `1/50000`, inner
height `100000`, outer height `25000000`, and gap `1/2`. Both adjacent
averages, smoothing loss, reciprocal mass, full infinite tails, and the
prime-power correction are included. Rational logarithm bounds suffice;
there is no numerical zero-location or prime-count assumption hidden in
these scalar calculations.

`DusartEarlierCutoff` joins these intervals to the existing infinite ray.
At that revision the canonical lower-band and checkpoint consumers in
`DusartVerifiedBootstrap` required finite theta data only through
`10000000000`, a reduction by a factor of 144.1 in the endpoint. Their
conclusion remains `HasThetaLogSquaredError (1 / 5) 3594641`. The checked
prime-count/log trace also feeds this shortened consumer. The old
trillion-endpoint trace interface remains available for compatibility.

This does not discharge the actual low-zero data: the bridge uses height
`25000000`, and the full infinite ray still requires height `1000000000`.
It does not supply the shorter finite count/coverage data, prime-counting
anchors, small prefixes, or final unconditional Dusart providers.

The full-range feasibility investigation rejected the current bulk-sieve
counting route before producing a large family. Primality certificates
prove selected primes but do not establish completeness of a prime count.
Pratt/partial-Pocklington proofs are useful for sparse witnesses; BPSW is
not used as a Lean primality oracle, and an external ECPP result is not
treated as a kernel proof. A practical complete counting implementation
for the remaining range still needs its own feasibility gate. The earlier
sieve source increment below is an exact interface, not a claim that its
trillion-scale replay is practical. CI builds remain paused.

Seven new or affected modules and ten focused Lean test files compile,
including both shared interval boundaries and the old trace interface.
All 29 audited theorem closures use only `propext`, `Classical.choice`, and
`Quot.sound`. All 180 Python tests, the fast checks, formatting, lint,
type checking, and workflow validation pass.

## Previous follow-up: exact local prime counts from a retained sieve (2026-09-23)

`SievePrimeCounting` now identifies the complete prime set from a certified
mod-six wheel bitset. It counts primes two and three separately, excludes the
bit representing one, and proves the exact final wheel-cell cutoff rather
than rounding an index up. Every smaller endpoint reuses the same sieve.
The new generic `Nat.bitCountBlock` has balanced splitting, exact bounded
finite-set semantics and an adjacent-block composition theorem.

`SievePrimeCountIncrements` counts only the bits between consecutive
endpoints. Its depth guard depends on that block's width, not on the whole
prefix. `SievedThetaPrimeTrace` transports the actual count from a proved
seed at three and feeds the earlier theta/log/coverage checks. The lower-band
consumer no longer assumes each endpoint's prime count separately. Numerical
sieve data and large-range feasibility still remain; no full family was run.

The reused sieve is `PrimeCert.Sieve.isSieve_of_sieveK_eq` at pinned commit
`916ee9c35a57af128d5089a69172415051e700ca` (Bhavik Mehta, Apache-2.0,
original Lean 4.33.0). Its producer requires `n <= 12884901888` and a sufficient
square-root bound. That limit is retained: it does not directly certify the
whole `1441000000000` lower-band endpoint. Larger coverage still needs a
segmented or suitably generalized certified producer, not a giant implicit
bitset or a weakened endpoint.

`Sieve`, `SieveCorrect`, `ForLean` and `ForMathlib` were inspected. No new
sibling search was required. On Lean 4.34 the pinned `ForMathlib` initially
failed because the multiplicity API changed. Its zero-modulus congruence
decomposition is actually false when multiplicity at zero is zero.
`scripts/patch_primecert_compat.py` adds the necessary nonzero premise and
passes the premise already present in the sole Pocklington caller, alongside
the two routine API ports. Both affected originals are fully validated at
the locked Git revision before writes; unrelated edits and caches are
preserved. Original notices and sieve/primality conclusions are unchanged.
Every Lean CI job applies this reproducible port. The sieve correctness and
Pocklington source modules compile under the pinned project toolchain.

All four new proof modules and both candidate facades compile; nine focused
Lean test files cover the complete small sieve/count/log/theta trace, offset
and zero-width counts, undersized-depth rejection, upper-range rejection,
and the zero-modulus compatibility counterexample. All 22 audited closures,
including the imported sieve and Pocklington conclusions, use only the
standard three axioms. All 177 Python tests and fast/workflow gates pass.
CI build jobs remain paused. These small regressions are not evidence for
the runtime of the large numerical families.

## Previous follow-up: compact prime-count transport for the lower theta band (2026-09-23)

The new candidate `Chebyshev.Intervals` derives the exact theta increment
and number of summands from Mathlib's prime-set difference, then bounds all
new logarithmic weights by the interval endpoint logs. This is a direct
reuse of pinned Mathlib finite sums and monotonicity, not a new prime-counting
estimate or a sibling theorem import.

`ThetaPrimeCheckpoints` retains each count and theta/log enclosure once.
Adjacent rational checks transport the accumulated theta enclosure with
outward rounding at every checkpoint. `CheckedThetaPrimeTrace` checks each
new endpoint logarithm using the prepared shared evaluator and composes
traces at their shared state. No per-prime logarithm certificates are needed.

`ThetaSquaredChecks` checks every adjacent margin and all fields of the
final endpoint. `DusartCheckedThetaTrace` feeds those checks into the actual
published lower-band theorem on `[3594641, 1441000000000]`. Exact prime counts
remain explicit inputs. This closes the transport and coverage interfaces,
not the numerical count tables or their large-range feasibility gate.

Five new modules and both candidate facades compile. The regression suite
includes actual count/log transitions through primes two and three,
zero/reversed endpoints, empty traces, malformed final endpoints and
rejected insufficient margins. The R6 scalar obligation is already closed
by the preceding increment. Actual high-height zero data, lower-band count
data and finite prime-counting/anchor providers remain outstanding.
All fifteen new theorem closures use only the standard three axioms;
all 170 Python tests and the fast/workflow gates pass. CI builds stay paused.

## Previous follow-up: all four R6 transform bounds certified (2026-09-23)

`ExpIntegralExpressions` preserves the exact five elementary integral
formulas, including the removable zero-exponent branches.
`KadiriTransformExpressions` assembles the complete signed transform;
`KadiriTransformChecks` connects its checked dyadic enclosure, including
every denominator-domain check, to the original four-point interface.

The four original points `0.09`, `0.69`, `0.79`, and `1` now have
kernel-checked lower bounds `18`, `22`, `23`, and `23`. One small module
reuses the existing row family and kernel constants. The tightest-point
representative passed in 6.2 seconds (peak process RSS about 4.32 GiB,
including imports); all four rows and both resulting endpoint chains
compile. No per-witness files, numerical axioms, or new integration
assumptions were introduced.

`DusartVerifiedBootstrap` supplies the real high-region, complete upper
theta-ray, and published-cutoff consumers without scalar-transform or
endpoint-chain hypotheses. The billion-height low-zero premise remains
explicit for the full theta route; the reduced twenty-five-million cutoff
is not substituted for it. Actual zero-verification data and coverage,
lower-theta checkpoints, prime prefixes/anchors and final unconditional
providers remain open. The R6 scalar bounds are no longer an open item.

All five new modules compile. Focused interface, zero-exponent, negative
exponent, denominator-rejection and existing downstream regression tests
pass. All 23 exported theorem closures use only the standard three logical
axioms. CI places expression semantics before numerical replay and keeps
the four-row certificate and its consumers serial in the certificate job.
Build jobs remain paused.

## Previous follow-up: checked complete Turing scalar margin (2026-09-23)

The exact smooth-integral difference now has a cancellation-aware rational
interval evaluator. Its shared constant `log(2*pi)` is charged only to the
difference of endpoint squares. The full proved counting-error budget is
included. A successful rational comparison gives precisely the existing
Turing completeness premise, with both height hypotheses and strictness
checked; the final theorem certifies every low-height divisor label from
valid ordered sign rows and the computed endpoint area.

`CheckedXiGridRows` connects shared endpoint vectors to ordered sign rows
using only adjacent index and sign checks, reusing Mathlib's finite-order
theorem and the existing append/area proofs. Placement and the scalar
margin feed actual low-height completeness directly. This closes those
interfaces, not the actual high-height data: numerical rows, coverage,
feasibility projections and other Dusart obligations remain. No sibling
reaudit or new zero-counting argument was needed. CI builds stay paused.

Both modules compile; 45 Lean examples across six files and ten theorem
closure audits pass, with only the standard three axioms. All 165 Python
tests and the canonical fast/workflow gates pass.

## Previous follow-up: complete rational error checks imply actual xi signs (2026-09-23)

The retained Fourier arrays now feed a short Horner enclosure, using an
independently proved generic semiring identity. The existing analytic Euler
tail has an exact scaled-factor form and a checked rational majorant; the
normalized Bernoulli coefficient sum is proved equal to its executable
finite formula. Complete recursive Fourier errors also have exact rational
semantics. No tail, moment, rounding, correction or Gamma term is omitted.

One shared check bounds all height-independent errors. Per-sample checks
then certify the short correction, scaled Euler remainder, elementary
phase, norm and strict sign margin. The assembler feeds the existing
actual-xi and exact-rational sign-row theorems. It neither assumes an RH
statement nor introduces a sign as a shared-data validity field.

Twenty changed/affected modules compile, 132 Lean examples in twenty-two
files pass, and all twenty-two audited closures use only the standard
three logical axioms. All 163 Python tests and fast/workflow gates pass.

Actual numerical rows, their coverage and the scalar Turing completeness
margin remain to be supplied. A representative high-height feasibility
gate remains required before any large family. Other Dusart obligations
and the paused CI build policy are unchanged.

## Previous follow-up: exact rational sign grids with real-radius moment checks (2026-09-23)

The moment assembler is shared by both the preserved rational-parameter API
and the new enclosed-real-parameter builder. Exact finite-sum and residual
coverage arguments occur once in `MomentChunkAssembly`. Retained blocks,
their rounding/append proofs and full-grid partition assembly are unchanged.

With radius `span/(2*pi)`, the original Fourier height is exactly the rational
ordinate `base+span*index/2^levels`; this reuses the previously proved
`ZetaGridPoint.height_of_radius`. Positive spans preserve all signed-index
orders. The exact endpoint identity now feeds the existing rational
`XiSignRow` verifier, while a proved reciprocal-pi interval supplies the
same radius enclosure to moments, corrections and phase checks.

Six new and four affected modules compile. The 91 examples across fourteen
files and thirteen theorem closure audits pass (standard three axioms only).
The complete reciprocal-pi-radius moment-to-grid adapter is exercised, as
are the preserved rational API and signed exact heights. Fast checks, Ruff,
mypy, all 162 Python tests and workflow validation pass.

The remaining sample obligation is executable value/error sign margins,
including every existing error term. No high-height data family or runtime
projection has been supplied. Other unconditional Dusart obligations and
the paused CI build policy are unchanged.

## Previous follow-up: checked elementary xi phase (2026-09-23)

`XiSimplePhase` replaces two argument evaluations and one complex-norm
logarithm with the elementary real-log expression, with a proved full error
of `33/(16*t)` at every positive height. The generic upper-right argument
bound is independently compiled in the candidate layer. The original
one-tenth Gamma remainder is not absorbed or dropped.

The optional checker prepares pi/log-pi intervals once, encloses real-height
logarithms by rational endpoint evaluations, and checks all numerical plus
analytical phase error by rational comparisons. Nonpositive height intervals
are rejected. `CheckedXiGridPhase` uses the same exact grid height for the
correction and phase checks and feeds the actual normalized-xi theorem.

All four modules, the candidate and affected facades compile. The 45 examples
in nine files and all nine public closure audits pass (standard three axioms
only), as do fast checks, Ruff, mypy, 161 Python tests and workflow validation.

Actual value/error sign margins, rational sign-row grid compatibility,
high-height data/completeness and performance projections remain. The
unconditional Dusart providers and paused CI policy are unchanged.

## Previous follow-up: actual checked Euler corrections (2026-09-23)

The short per-sample correction now has an executable interval checker.
The candidate `Polynomial.bernoulliNormalizedReal_zero` connects all
normalized endpoint coefficients to the exact rational Bernoulli numbers,
including the sign convention at index one. `ZetaEulerFactor` factors the
existing correction without changing any term or its complete remainder.
The numerical layer shares endpoint logs/amplitudes and the Bernoulli
coefficient list, then evaluates one successive rising-factor recurrence.

The checker accepts enclosed real heights, including the actual Fourier
pi-grid heights. A failed squared-norm positivity test rejects inversion;
successful tests bound the complete complex correction error. The
`RationalGridPoint.valid_of_check` adapter proves both mathematical sample
premises, and its zeta consumer retains the existing full error budget.

All six new modules and the updated complex-interval module compile.
The 78 regression examples across thirteen files and all 20 public theorem
closure audits pass; the closures contain only the standard three axioms.

This does not supply high-height sign/completeness data or a runtime
projection. The rational-endpoint sign rows still need an exact compatible
grid parameterization, and elementary xi-phase/sign checking remains.
The other unconditional Dusart obligations and paused CI policy are unchanged.

## Previous follow-up: checked shared Dirichlet moments (2026-09-23)

The optional numerical layer now constructs actual shared-moment enclosures.
`SharedTaylorIntervals` prepares the scalar Taylor lists and logarithm-of-two
interval once. `DirichletAtomIntervals` computes each positive integer's
logarithm once and reuses it for amplitude, residual frequency and phase.
Integer-period reduction uses an explicit proved pi enclosure and Mathlib's
exact sine/cosine periodicity. The integer shift need not be trusted as a
rounded transcendental value. No coarse fixed-pi reduction is used.

`ComplexInterval` reuses LeanCert's real interval arithmetic for complex
rectangles and complete Euclidean error tests. The generic Taylor-atom
recurrence is independently proved in the Mathlib candidate layer.
`MomentIntervalColumns` materializes the successive orders as one array;
`MomentChunkIntervals` shares each atom across every requested column and
proves the exact finite Dirichlet-moment error from rational comparisons.

`DirichletMomentBlock.Valid.append` merges adjacent same-bin chunks using
only retained coefficients and errors. Checked outward rounding can shorten
those retained rationals without replaying atoms. `MomentBlockPartition`
checks endpoint coverage, with adjacent decreasing-label checks supplying
global uniqueness without quadratic duplicate scanning. Its fiber theorem
identifies every complete-prefix frequency group with the corresponding
block. `CheckedZetaMoments` feeds these bounds into the actual grouped-block
validity and the existing rational Fourier checker.

All ten modules and affected facades compile; 121 examples across eighteen
new/preserved files and all 41 public theorem closure audits pass. Only the
standard three logical axioms occur. Ruff, mypy, all 159 Python tests and
workflow validation pass. The checked unit grid exercises the full adapter,
but does not stand in for a representative high-height runtime benchmark.

This supplies the non-generated checker and composition proofs, not the
large numerical moment/trace family. Short per-sample Euler corrections,
actual signs/completeness margins, numerical R6 bounds, lower theta data,
finite prime prefixes/anchors and the unconditional providers still remain.
Representative nontrivial high-height runtime and precision projections are
still required before generating a large family. CI builds remain paused;
the new build/test steps are ordered for their eventual re-enablement.

## Newest follow-up: executable rational Fourier checks (2026-09-23)

The shared radix interface now has executable rational arithmetic checks.
`Complex.RationalPoint` supplies exact Gaussian arithmetic and an equivalent
Boolean squared-norm test, with nonnegative error budgets enforced. A
`RationalTrace` checks every leaf, right-output cap and arithmetic merge.
One twiddle table per depth is shared across every node and Taylor column;
the canonical root-square identity discharges parent/child compatibility.

`RationalAlias` uses explicit frequency lists and two sparse rational
coordinate passes. This matters for executability: the earlier mathematical
alias definition uses noncomputable `Finset.toList`. The new list-based
assembler proves equality with that exact complex alias array. Duplicate
frequency rows are rejected, while distinct frequencies colliding modulo
the transform size are added and retained.

The optional twiddle checker reuses LeanCert's proved direct sine/cosine
Taylor enclosures, together with Mathlib's twenty-digit pi bounds. It checks
the full Euclidean error using endpoint radii, without the coarse fixed-pi
large-angle reduction. `CheckedZetaGrid` verifies list uniqueness, shared
twiddles and every required rational transform column, then derives the
existing `ZetaGridBlock.Valid` and actual zeta error theorem. No semantic
Fourier-input equality or phase enclosure remains an unexplained input to
that checked adapter. Shared moment enclosures and the short per-sample
correction still have to be supplied and proved.

The original unbounded analytic import closure remains independent of
LeanCert. The optional rational checker bridge directly imports only
`LeanCert.Core.IntervalRat.Taylor`, not its tactics or project certificate
replays. Tiny regression checks use `decide +kernel`: ordinary elaborator
reduction stops at Lean's deliberately irreducible rational operations.
The source checker and its soundness proof introduce no native-evaluation
shortcut. No large numerical family has been generated or replayed.

Still needed are actual moment enclosures, rounded trace data, sample
corrections/signs, completeness margins and representative high-height
resource projections. The fixed twenty-digit pi enclosure is explicit;
this increment does not claim that it suffices for every numerical margin
or that a high-height kernel replay has been benchmarked. The other
unconditional Dusart and all-k obligations remain unchanged.

All six proof modules and both affected facades compile. The 72 examples
across eleven new/preserved files pass, including successful and rejected
kernel checks and a complete checked unit grid. All 23 public theorem
closures contain only the standard three logical axioms, including the
transitive LeanCert trigonometric proofs. Fast source checks, Ruff, mypy,
all 155 Python tests, Ruby metadata and workflow checks pass.

## Newest follow-up: shared radix-two grid evaluator (2026-09-23)

`Fourier.radixTwo` now implements the finite transform with materialized
even/odd half-transforms and a successive-power twiddle table. The complete
finite-sum identity is proved for every depth and every root with the required
period, without a primitivity assumption. Its butterfly-output recurrence is
exactly `n * 2^n`; this counts butterfly outputs, not total machine instructions
or Lean replay time. Mathlib's `ZMod.dft` and additive character identify its
positive-phase convention with the DFT at the negative index.

All integer frequencies, including negative ones and modulo-grid collisions,
are retained. `Vector.scatterAdd` accumulates sparse coefficients through one
array update per row, with entry and append theorems. The actual alias array
uses that accumulator instead of filtering every input for every output.
One transformed coefficient array per Taylor order then serves every grid
sample. This avoids independently recomputing the long prefix or transform
at each candidate zero endpoint.

The recursive `RadixTrace.Valid` interface checks every leaf and merge while
sharing output and twiddle arrays. Its assembler proves the complete uniform
error, including input, phase/twiddle and arithmetic errors at every level.
`ZetaGridEvaluation` combines these errors with the already-proved shared
moment and full Euler bounds. `XiGridEvaluation` feeds the existing normalized
xi/phase machinery and the actual sign-row verifier in either orientation.
The exact grid-height theorem permits rational arithmetic-progression
endpoints by choosing the block radius appropriately.

This is a proved implementation and error assembler, not completed numerical
zero verification. Actual moment enclosures, rounded trace data, numerical
sample signs, completeness margins and a representative high-height replay
projection are still required. No numerical certificate family was generated
or replayed, and no high-height runtime claim is made. The original middle/far
ray cutoff and the other unconditional Dusart obligations are unchanged.

All eight proof modules and the candidate facade compile; 76 examples in
thirteen new/preserved regression files pass. All 27 audited public theorem
closures contain only the standard three logical axioms. The tests include
empty/one-point grids, repeated and negative frequencies, nonprimitive roots,
nonzero twiddle errors, negative-error rejection and actual sign/Turing
consumers. CI checks the candidates and consumers sequentially. Fast source
checks, Ruff, mypy, all 153 Python tests, Ruby metadata and workflow checks pass.

## Newest follow-up: shared frequency-group evaluations (2026-09-23)

The actual zeta evaluator now separates a block's long positive Dirichlet
prefix into reusable moments of grouped logarithmic frequencies. Mathlib's
finite fiber sums, exponential Taylor remainder and complex-power identities
give the exact regrouping and complete error. The four general candidates
live entirely in the Mathlib candidate layer; the actual zeta and xi consumers
reuse the existing Euler expansion, WIP Bernoulli tails, normalized xi phase
and sign-row verifier. No zero indexing or counting foundation is rebuilt.

Each block supplies explicit integer bins and checked moment enclosures.
Every sample in its normalized unit window reuses those coefficients and
supplies only group phases and the short Euler correction. The residual
frequencies have magnitude at most one half, giving the uniform truncation
bound `N * (1/2)^degree * exp(1/2)`. Every stored-moment error, phase error,
short-correction error and the complete Euler remainder remains in the
actual zeta bound. Separated real xi intervals feed `XiSignRow.Valid` in
either sign orientation. Nearest-integer bins are only a convenience
specialization; the actual consumer does not require evaluating an exact
floor of a transcendental logarithm.

These are analytic approximation and sign implications, not computed finite
zero verification. No moment data, actual sign samples or completeness
margin is supplied by this increment. It is not yet a fast Fourier evaluator
or a high-height runtime result: building and checking shared coefficients
and efficiently evaluating a whole grid remain implementation obligations.
The previous billion-height middle/far-ray requirements are unchanged.

All seven new proof modules and the five affected candidate facades compile.
The 69 examples across twelve new/preserved regression files pass, including
empty sums, degree zero, nearest-integer ties, a negative window endpoint,
zero-cutoff rejection, an explicit valid unit block and the actual sign-row
and reduced Dusart consumers. All 25 audited public theorem closures use
only `propext`, `Classical.choice` and `Quot.sound`. CI builds each new
candidate and consumer sequentially with its regression test.
Fast source/architecture checks, Ruff formatting and lint, mypy, all 152
Python tests, Ruby metadata checks and workflow validation pass. No finite
certificate generation or replay was run.

## Newest follow-up: height-uniform R6 admissibility and common chain (2026-09-23)

The existing R6 row and correction proofs now apply at every real cutoff
`T>=25000000`. The common separation parameter is `437/1000`; the proved
scale and real-coordinate bounds are `eta<=98/10000` and `sigma>=9922/10000`.
Both exact kappa inequalities, all pole and complete harmonic-tail budgets,
the negative Gamma residual and the complete correction sign are proved on
this wider domain. No numerical correction premise remains after the
existing shared kernel/support enclosures are supplied.

The argument comparison reuses the already proved monotonicity of
`log(T)/log(16*T+100000)`. One four-point family, now at `0.09`, `0.69`, `0.79`
and `1`, supplies a single chain assembler for every starting constant
between eight and sixty-nine. The original `56 -> 8 -> 6.5 -> 6` billion-height
interface and the reduced `69 -> 8 -> 6.5 -> 6` interface both call it.
The actual reduced region consumer connects this chain to the existing
finite sign-row/Turing verifier. No second certificate family was added.

The four numerical transform bounds and actual finite sign/completeness
inputs remain unproved here. The middle/far psi estimates still use height
one billion. In particular, the current middle-tail expression cannot be
reused by merely replacing its cutoff: a floating diagnostic at `log(x)=800`
gives a scaled high-tail budget about `344.86` at height 25000000, versus its
required allowance `0.059`. This is diagnostic evaluation, not a Lean
theorem or a claim that every alternative analytic argument must fail.
The original billion-height chain remains available for the existing ray.

All 13 affected analytic modules compile; 60 regression examples in 13
files pass, retaining the original whole-ray consumer tests and adding the
new boundary and reduced-chain interfaces. All 37 audited public theorem
closures contain only the standard three logical axioms. Fast checks,
Ruff, mypy, all 151 Python tests, Ruby metadata and workflow checks pass.
No finite certificate generation or replay was run.

## Newest follow-up: half-mass reuse and reduced psi verification height (2026-09-23)

`XiPositiveReciprocalMass` uses the existing multiplicity-preserving
conjugation and unconditional real reciprocal mass. A positive prefix and
its conjugate image are disjoint and have equal sums; their union is bounded
by the complete mass. Consequently the positive prefix needs only half that
mass. No RH premise, new zero enumeration or sibling dependency is introduced.
`XiLowReciprocalNormBound` now uses this improvement in its actual bound.

`XiReducedCutoffBounds` proves explicit logarithmic and power-tail bounds
for inner height 1250000 and outer height 25000000. The order-five smoothing
step 1/600000 then proves the same psi margin `1/36260` for every real
`x>=1441000000000`, requiring critical-line verification only below 25000000.
The original billion-height psi theorem now derives from this stronger
theorem. The middle-band theta consumer uses the same improved interface.
All scalar caps are proved inequalities, not numerical projections.

`DusartReducedZeroVerification` feeds the existing finite sign-row/Turing
verifier into these actual psi and theta estimates. Its starting region
constant 69 at height 25000000 follows from the proved bounded initial
region, without a low-zero premise. A supplied valid endpoint chain can
improve that region; this does not assert the chain's numerical margins.

This reduces the psi endpoint's verification height by a factor of forty,
not the entire project's height requirement. The concrete R6 rows and
far/middle-ray estimates still use height one billion. Their numerical
admissibility, actual finite zero signs/completeness, the lower theta band,
prime-counting prefix and final unconditional providers remain open.
No finite certificate generation or replay is involved in this increment.

All 57 affected/new analytic modules compile; 289 regression examples in
55 files pass. All 32 audited public theorem closures contain only
`propext`, `Classical.choice` and `Quot.sound`. Fast source checks, Ruff
formatting/lint, mypy, all 150 Python tests, Ruby metadata tests and workflow
validation pass. New CI build and regression steps are sequential.

## Newest follow-up: moderate-height Lehman and bootstrap domain (2026-09-23)

The existing proved `log(T)+17` counting discrepancy already applies near
height ten. The billion-height cutoff in the harmonic tail came from the
additional simplification `log(T)+17 <= 2*log(T)`, not a zero-location theorem.

The reciprocal-square-pair integration-by-parts candidate now retains an
arbitrary additive constant in its logarithmic weight. `XiLehmanLogBound`
applies it with constant seventeen to the complete improper integral.
The strict boundary count absorbs all closed-cutoff multiplicities, without
assuming that the cutoff is not a zero ordinate. Its elementary bound is
the exact main integral plus
`(2*log(t+H)+34)*(1/H^2+1/(H+2*t)^2)+2/(t*H)` for `t+H>10`.
At `log(t+H)>=17`, this is no larger than the former high-height expression.

The signed harmonic majorant uses this bound, retaining the existing exact
finite mass subtraction at height zero. Its affine envelope reserves the
additional `68/H^2` constant explicitly. The actual master, correction and
uniform/split/grid bootstrap theorems propagate the weaker height premise
through `KadiriEndpointRow.Valid`, whose height condition is now `10<=T`.
The original billion-height initial-region theorem remains unchanged.

`KadiriInitialCutoff` reuses that initial region and its already proved
bounded-strip extension. It derives the explicit initial constant `504/n`
at height `10^n` for every integer `1<=n<=9`, without a finite zero-location
premise. For example, constants 63, 72 and 84 apply at heights `10^8`, `10^7`
and `10^6`, respectively. The endpoint-chain consumer discharges its
starting-region premise using this theorem; improved-region numerical
margins and the low-height input remain explicit.

This does not establish numerical row admissibility at height ten or replace
finite critical-line verification. The existing concrete R6 rows and psi
endpoint still use height one billion. Lowering that computational cutoff
requires new admissibility and psi-budget bounds; changing this analytic
domain alone is insufficient. No finite certificate generation is involved.

All 97 affected/new analytic and candidate modules compile. The 338 focused
examples in 66 files pass, including the existing concrete R6 and conditional
Dusart consumers. All 24 audited public theorem closures contain only
`propext`, `Classical.choice` and `Quot.sound`. Fast source checks, all 149
Python tests, Ruff formatting/lint, mypy, Ruby metadata tests and workflow
validation pass. The new CI build and regression steps remain sequential.

## Published sibling update inspected (2026-09-23)

The public WIPResearch head is now
`10607f234b2e5a64345bd49c7f21f80a419bc818`, following the previously reviewed
`bdc46941c4f2e13fb84e0a338b905bb10e711357`. Robin and BV heads are unchanged.
The newer WIP sources include explicit logarithmic-phase correlation and
integer-multiplicity sum bounds, and additional BKLNW band consumers.
These are further reuse candidates, not a newly pinned dependency or a claim
that their complete closures have been ported and audited here.

In particular, `BKLNWClassicalZeroFreeEnvelope` retains an existential region
constant; `Zeta23ZeroFreeBridge` retains an existential logarithmic-power
constant; and `BKLNWHeightBandDensityExplicit` requires a supplied
`zero_density_bound` and band-region hypotheses. Those inspected statements
do not supply the missing finite-height critical-line verification. The
previously extracted Bernoulli and conjugation leaves remain in use.

## Newest follow-up: compact lower-theta and anchor interfaces (2026-09-23)

Mathlib's `Chebyshev.theta_mono`, logarithm monotonicity and elementary
positive-power comparisons suffice for the remaining real-interval adapter.
The existing endpoint rows target different Dusart margins, so they do not
by themselves prove the required coefficient `1/5` with two log powers.

`ThetaSquaredCheckpoints` and `ThetaSquaredChain` derive that exact bound
from shared rational endpoint enclosures and ordered pair margins, including
all noninteger points and both boundaries. The same endpoint data feeds
`DusartCheckpointAnchors`, reducing both Abel anchor obligations to rational
polynomial comparisons plus a prime-counting enclosure. The final consumer
reuses the proved Turing/region ray and the published-cutoff adapters.

The four modules compile, all 32 focused examples pass, and all ten public
theorem closures have only the standard three axioms. No new sibling
dependency, finite data generation, or certificate replay is involved.
Actual numeric enclosures and margins remain unproved inputs; this is not
a claim of a closed lower-theta band or completed Dusart provider.

## Previous follow-up: higher-order evaluation from WIP Bernoulli tails (2026-09-23)

The Mathlib-only leaf `RobinBV/Mathlib/NumberTheory/BernoulliPeriodic.lean`
from WIPResearch commit `bdc46941c4f2e13fb84e0a338b905bb10e711357`
(Jonas Whidden, Apache-2.0, originally Lean 4.33.1) is extracted into four
small candidate modules: normalized profiles, integrability, integer cells
and complete tail recursion. Original `Polynomial` declaration names are
retained. The extracted proofs compile on the pinned Lean 4.34 toolchain.
Their import closure is entirely Mathlib; the tail-recursion axiom audit
contains only `propext`, `Classical.choice` and `Quot.sound`.

`BernoulliPeriodic.ExplicitBound` replaces the existential compactness bound
with the rational sum of absolute normalized polynomial coefficients.
`ZetaEulerTail` adapts WIP's zero-point Euler expansion to arbitrary points
with positive real part, using the already-audited PNT continuation formula.
No zero or RH hypothesis is introduced. `ZetaEulerApproximation` proves the
exact arbitrary-order expansion and its complete explicit error, retaining
every Bernoulli boundary term and the full remaining integral.

`XiNormalizedCriticalLine` removes a strictly positive amplitude from xi.
The rotation-error candidate and `XiEvaluationError` propagate independent
phase and zeta errors. The existing Gamma remainder supplies the explicit
Stirling phase, and `XiEulerEvaluation` turns separated error intervals into
actual xi sign changes. Its rounded-evaluation interface explicitly adds
the finite complex-value and elementary-phase errors to both analytic
remainders. These are analytic theorems for all real heights,
positive cutoffs and arbitrary orders, not a finite zero-verification result.

Still needed: certified finite evaluations, including rounding of elementary
functions, a feasible high-height evaluation strategy where direct summation
is too long, the actual sign samples, and their completeness margin. This
increment does not assert that a high-order O(N) sum solves high-height cost.
No finite replay or new dependency is introduced.

All thirteen proof modules and affected facades compile; 72 examples across
sixteen new/preserved regression files pass. All 44 public theorem closures
use only the standard three axioms. The sequential foundation CI chain checks
each candidate before consumers. Fast source checks, all 147 Python tests,
Ruff, mypy, Ruby metadata tests and workflow validation pass.

## Previous follow-up: exact phase bound and unconditional counting budget (2026-09-23)

The phase correction now reuses the proved shifted Gamma Stirling error and
Mathlib's elementary logarithm and tangent bounds. The squared norm gives
the decaying correction instead of the earlier constant triangle bound;
the pole argument retains its correct upper-left-quadrant branch.
No zero indexing, summability or sibling region result is reconstructed.

The actual counting remainder has the unconditional upper integral budget
`(15/16)*(b-a)+((19/2)*log(5*b)+95)/pi` for `32<=a<=b`.
The exact counting normalization and Littlewood identity are reused without
dropping their `7/8` offset. The existing finite missing-label verifier now
accepts an explicit endpoint margin and sign rows, with its analytic
counting-error premise discharged. Actual Dusart region/theta consumers
use that strengthened verifier.

Finite numerical signs and margins, lower theta verification and the final
unconditional providers remain open. This proves the analytic count budget,
not a computed finite critical-line result. No new sibling dependency or
finite certificate replay was introduced.

The five proof modules and affected facades compile. All 33 regression
examples and 11 standard-axiom closure audits pass; fast checks, 145 Python
tests, Ruby metadata validation and workflow checks also pass.

## Previous follow-up: complete Littlewood identity and continuity through zeros (2026-09-23)

The remaining continuity proof reuses Mathlib's
`MeromorphicOn.extract_zeros_poles_log`, compact divisor finiteness and
finite meromorphic order on connected sets. It introduces no new zero
enumeration, multiplicity machinery or sibling dependency. Project-independent
adapters isolate the horizontal factorization and continuous-integral steps
in the candidate layer before their zeta and Turing consumers.

The full right-tail derivative directly reuses Mathlib's von Mangoldt
Dirichlet series, improper FTC and dominated differentiation. No finite
tail truncation or new numerical certificate is needed. The actual
Littlewood identity now holds across all positive zero heights, and both
complete horizontal bounds give the explicit argument-integral budget
`(19/2)*log(5*b)+95`. The exact Gamma/pole correction to the counting model
is retained; low-zero completeness does not follow from dropping it.

The focused sibling check reconfirmed the reuse already recorded below:
Robin/PNT inverse-square summability, BV conjugation order and existing
weighted/divisor infrastructure are not being reconstructed. The inspected
WIP shifted norm-mass identities retain RH, while local-count bounds have
existential constants. No blanket absence claim about sibling results is
made. The current new proof instead applies the exact pinned Mathlib
factorization theorem needed at the remaining analytic boundary.

All twelve production modules and affected candidate facades compile.
The 79 regression examples and all 29 standard-axiom closure checks pass.
Fast checks, Python/Ruby tests and workflow validation pass without finite
replay. Smooth phase bounds and actual numerical low-zero verification
remain required for the final Dusart providers.

## Previous follow-up: actual counting phase and finite log derivative (2026-09-23)

The existing surrogate counting contour, Euler logarithm, Gamma primitive,
actual divisor countability and strict/closed count bridge give the exact
normalization `pi*N = argument + phase`. The pole's principal logarithm
is used only on positive-height horizontal lines, where it avoids its cut;
zeta's argument is its Euler-normalized contour variation, not its principal
logarithm. The phase is `Im(xiGammaLog(1/2+iT)) + arg(-1/2+iT)`.

Countable zero ordinates are a null set, so the normalization integrates
across zero heights and gives the actual closed-count discrepancy with its
exact smooth-phase correction. The existing main term still has no `7/8`.

For the derivative of the finite horizontal log-modulus integral, Mathlib's
squared-norm derivative supplies the branch-independent pointwise formula.
Its compactness and dominated differentiation theorems supply the uniform
majorant on a rectangle constructed from regularity of a single height.
The two general adapters are isolated in the Mathlib candidate layer and
built before the consumer. No additional sibling import, RH premise, or
finite replay is introduced. This reuses the previously audited analytic
infrastructure rather than constructing another zero enumeration.

All six modules and the affected candidate facades compile; 58 regression
examples and 23 complete standard-axiom closure audits pass. The fast,
Python, Ruby and workflow checks pass, without finite replay.

Still required for Littlewood's identity: the derivative of the complete
infinite right tail and the passage through exceptional heights. The finite
derivative and integrated count normalization alone do not prove that identity
or complete low-zero verification.

## Newest follow-up: actual log-ratio and full horizontal lower bound (2026-09-23)

No new sibling audit or dependency is needed for this step. The xi product
and divisor finiteness are already available. The pinned PNT
`Complex.norm_weierstrassFactor_div_sub_one_le_pow_div` supplies the factor
bound; its `Hadamard.DivisorConvergence` finite-exception argument works
directly with the actual multiplicity labels. The exact source revision is
`f6147e7572ab3abe5428101bc0b13627bcb005df`. No bijection with the natural
numbers or unproved infinitude of zeros is introduced merely to use the
sequence-indexed summability theorem.

Mathlib's `Summable.summable_log_norm_one_add`,
`Real.rexp_tsum_eq_tprod`, and `Multipliable.norm_tprod` identify the full
product logarithm. The existing unconditional real Hadamard constant
cancels the regularization. Existing actual-divisor countability and the
Bochner-series candidate justify integral interchange; endpoint zeros are
excluded almost everywhere using `exists_xi_divisor_index_of_zero`.

The already proved `DigammaHeightBounds` and `XiGammaContour` control the
Gamma increment. The nonnegative pole gain reuses `Complex.logNormStep`.
Together with both existing infinite-tail budgets, these prove the actual
horizontal lower bound `J(T) >= -8*log(abs(T)/2+3)-94` for `T != 0`.
All seven modules compile; 65 regression examples and 27 complete axiom
closure checks pass. Only the three standard logical axioms occur.
There is no finite replay, RH input or new numerical boundary assumption.
The Littlewood/Turing count identity and numerical zero verification still
remain; the horizontal bounds alone do not establish finite RH or Dusart.

## Previous follow-up: logarithmic kernel and complete spectral budget (2026-09-23)

The public Robin, BV and WIP heads were rechecked. The current WIP counting
and region modules retain existential constants, and its inspected exact
shifted norm-mass identities retain RH. No existing numerical Turing bound
was identified in those sources. Their unconditional infrastructure remains
usable; no blanket claim about missing or incomplete sibling proofs is made.

The new kernel proof applies Mathlib's meromorphic log-integrability,
exact real logarithm primitive, `self_sub_one_le_mul_log`, and
`log_le_sub_one_of_pos`. An almost-everywhere comparison excludes the real
singleton singularity. Low- and high-imaginary-part bounds prove a uniform
constant sixteen in the paired resolvent inequality, without the computed
rectangle boundary used for Booker's optimized constant.

The actual xi consumer reuses `riemannXiDivisorSameHeightReflection`,
`summable_re_xi_divisor_resolvent`, and the unconditional real Hadamard
constant cancellation. It neither reconstructs the divisor nor assumes
all zeros have real part one half. Existing `ZetaRealPole` and
`DigammaExplicitBounds` then give the complete integrated-step budget
`8*log(abs(T)/2+3)+88`. No new sibling dependency or finite replay is added.

The seven modules compile, all 54 regression examples pass, and all 22
audited closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
The log-ratio identity, integral interchange and actual counting discrepancy
estimate still require proof; the spectral budget alone is not a Turing
verification or an unconditional Dusart provider.

## Previous follow-up: actual horizontal logarithmic integrals (2026-09-23)

The finite-segment logarithmic singularities require no new general proof:
Mathlib's `MeromorphicOn.intervalIntegrable_log_norm` handles them directly.
Its cross-field `MeromorphicAt.comp_analyticAt` and the analytic real
embedding specialize it to horizontal zeta segments. The new horizontal
series bound uses `LSeries.norm_term_eq`, `LSeriesSummable.of_re_le_re`,
real-power monotonicity and summable norm comparison. The existing Euler
logarithm then supplies both signs of the actual logarithmic modulus.

The actual upper bound uses the previously audited PNT Euler-continuation
leaf through `norm_riemannZeta_le_euler_one`, and the proved real-axis pole
bound. The complete infinite tail is bounded, not truncated. The shift
identity reuses interval-integral translation and additivity, preserving
both right-hand contributions and avoiding a nonvanishing premise at every
point. No RH-based zero mass or new sibling dependency is introduced.

The sibling capability index and the inspected WIP coefficient-normalization
module do not provide this horizontal support-decay interface. These new
candidates instead apply the pinned Mathlib lemmas above directly. The
quantitative lower shifted integral and the count-to-horizontal-integral
identity remain required; this increment is not finite RH verification or
the final Dusart theorem.

The five modules and affected candidate facades compile. All 56 regression
examples and 20 complete standard-axiom closure checks pass. The analytic
chain has no generated or finite-replay dependency.

## Previous follow-up: integrated missing-count verification (2026-09-23)

The completeness argument reuses the actual positive-height finsets,
their monotonicity, the existing critical-line row witnesses, and the
proved conjugation/real-axis reduction. Mathlib's monotone integrability
and integral comparison show that an omitted lower label contributes at
least the interval width. No new divisor index or zero-location assumption
is introduced.

The already compiled `FinsetAbel` candidate supplies the clipped row-count
integral after specialization to the identity function. Rational block sums
compose with `Fin.sum_univ_add`, and the existing counting model is integrated
by elementary differentiation and FTC. Actual region and theta consumers
now accept the resulting integral budget as an alternative to an exact count.

This proves the verification implication, not its analytic discrepancy bound
or the endpoint signs. The Turing bound from Trudgian's arXiv:0903.1885 is not
imported as an assumption-free theorem. Our count model omits `7/8`, so its
remainder must not be equated with the paper's argument term without proof.
No RH-dependent sibling mass evaluation or new sibling dependency is used.
The published sibling revisions are unchanged from the preceding audit.

The candidate and actual consumers compile; 76 regression examples and
26 complete standard-axiom closure checks pass. These are non-certificate
builds and do not claim the missing numerical verification.

## Previous follow-up: finite critical-line exhaustion (2026-09-23)

The new sign/count verifier reuses `exists_xi_divisor_index_of_zero`, the
actual strict positive-height count, multiplicity-preserving conjugation,
and real-axis nonvanishing. It does not introduce another zero enumeration
or assume that distinct complex values exhaust the divisor labels.
Mathlib's intermediate value theorem supplies the critical-line zeros;
`Finset.card_image_of_injective` and `eq_of_subset_of_card_le` provide the
finite exhaustion step. No new general cardinality lemma is needed.

Compact rational row blocks concatenate, and an endpoint-sequence adapter
shares the data at adjacent boundaries. The reusable proof derives the
exact low-height hypothesis required by the existing Dusart consumers.
Actual numerical sign verification and a matching total-count upper bound
remain open. This is not an unconditional finite critical-line result,
nor a new RH-dependent sibling import. No sibling revision or dependency
has changed in this increment.

All four modules compile; 44 regression examples and 21 complete axiom
audits pass. The audited closures contain only the standard three logical
axioms. The source remains in the non-certificate CI job.

## Previous follow-up: uniform correction and four rational transform points (2026-09-23)

The remaining correction sign now follows from existing height-decaying
Gamma and complete Lehman bounds, the exact polynomial coefficient mass,
and elementary inequalities. The proof is uniform over all three bootstrap
steps and includes zero scale. It introduces no new zero counting, pairing,
or summability machinery and no assumed numerical correction.

The existing signed-transform endpoint-minimum theorem reduces the moving
arguments to four rational points, after their logarithmic interval bounds
are proved. One `Fin 4` family and the existing ordered-chain assembler
cover all three steps. The four scalar validity inequalities remain explicit
inputs; they have not been evaluated here. The same finite low-height
critical-line condition is still required by the actual region consumer.

The published sibling heads still match the previous audit. Source checks
reconfirmed Robin's unconditional inverse-square summability leaf, its
RH-dependent exact norm-mass theorem, BV's existential region constant,
and WIP's existential logarithm-ninth region. The existing reuse remains
applicable; none of these inspected statements supplies the missing explicit
region at six or finite critical-line verification by dropping a hypothesis.

The six modules and candidate compile, all 39 regression examples pass,
and all 21 audited closures contain only the three standard logical axioms.
The new source remains in the non-certificate CI job, with no finite replay
dependency and no new sibling dependency.

## Previous follow-up: one-cell bootstrap and exact polynomial checks (2026-09-23)

The existing elementary grid theorem already covers a one-cell scale domain.
`KadiriEndpointRows` uses it directly and composes checked improvements with
Mathlib's reflexive-transitive closure. No new zero indexing, pairing,
counting, or summability machinery is introduced. The actual initial region
at 56 is reused in `KadiriR6Bootstrap`.

The exact published generating sequence is stored once as rational data.
One finite sign check and a shared cast supply the actual real polynomial
coefficients; its existing global nonnegativity proof is unchanged.
The common parameter ranges and both kappa constraints are now proved.
Small explicit LeanCert dyadic rows provide the kernel and support bounds;
their Boolean premises use kernel replay, and domain validity is checked.

The proposed three-step chain still needs its correction and transform
inequalities. `DusartSquaredBootstrap` connects a checked chain to the
actual theta estimate, but does not assert the chain or finite low-zero
verification. No RH-dependent sibling mass formula or new sibling dependency
is introduced; the previously recorded reuse boundary remains unchanged.

## Previous follow-up: the middle band and complete conditional analytic ray (2026-09-23)

The fixed-cutoff tail already retained the full fourth height power.
Its closed expression now has an explicit coefficient and exponential
damping across the whole middle band, without zero-window enumeration.
Mathlib's `log_le_sub_one_of_pos` gives the global damped-monomial maximum;
the existing after-turning-point theorem alone would not cover this band.
Both actual averages reuse the established fixed-height Rosser API and
their correct separate normalizations.

The actual theta coefficient `1/5` now holds on the full ray above
`1441000000000`, conditional on the same finite low critical-line input
and numerical high region `R=6`. Neither zero-location input is supplied
by this increment. The lower bounded band, finite prime prefixes and
anchors remain unfinished. No new sibling dependency, RH-based mass
evaluation or assumed scalar margin is introduced.

The seven modules, extended candidate and affected facades compile.
All 47 regression examples pass; all 24 audited closures contain only
the three standard logical axioms. The new analytic chain has no finite
replay dependency and is built serially before certificates in CI.

## Previous follow-up: evaluated far-ray bound using existing zero sums (2026-09-23)

The far-ray estimate reuses the actual sharp Rosser budget and both adjacent
psi averages. Mathlib's logarithm-over-power monotonicity supplies the new
damped-monomial candidate. Explicit bounds at root parameter 28 discharge
the entire scalar budget, including its complete high tail; no sibling
zero machinery is reconstructed. The shifted lower average retains its
own root, step and normalization.

The actual theta estimate has coefficient `1/5` above `exp(5000)`, subject
to finite low critical-line verification and the high region `R=6`.
Both zero-location inputs remain unproved. The existing unconditional
constant `56` is not silently substituted for six. The remaining middle
and lower bands, finite prime prefixes and anchors also remain explicit.

Published main refs were rechecked: Robin1984 remains `acab1a31f31e0499518a4416b63281e0b4838f9c`,
BV remains `7a1748306e026825ed6a5555516cc2f28989b2ac`, and WIPResearch remains
`10607f234b2e5a64345bd49c7f21f80a419bc818`. The source-inspected WIP region
bridges retain existential constants; the inspected exact norm-mass
evaluations retain RH. No new sibling closure is imported or claimed audited.

The candidate, seven project modules and affected facades compile. All 43
new or preserved regression examples pass, and all 27 newly audited theorem
closures contain only the three standard logical axioms. This increment
has no finite-replay dependency.

## Previous follow-up: direct log-square adapters and a proved middle band (2026-09-23)

The direct prime-counting route reuses `dusartJ_sandwich`, its already
proved derivative, and the existing logarithmic derivative candidates.
Comparison with the exact two-term models requires only theta error
`0.2*x/log(x)^2`, not the older stronger log-cubed/log-fourth interfaces.
The short-interval route reuses `exists_prime_of_theta_increment` at the
requested width. Both adapters specialize to the published cutoff
`3594641`; all derivative margins and logarithmic side conditions are proved.

The normalized psi-to-theta comparison is extracted from the existing
theta-margin proof without changing its interface. It combines the actual
psi endpoint and root correction to prove the log-square theta error on
`[1441000000000, exp(85)]`, retaining only the existing finite low-zero
condition. All zero summability, counting and reflection arguments are
reused unchanged. No new sibling audit, import or RH-dependent mass
evaluation is involved.

The global log-square estimate, low-height verification, finite prefixes
and exact prime-counting anchors remain open inputs. These adapters do not
claim those inputs or the three unconditional Dusart providers.

The six new modules and refactored consumer compile. All 38 new or
preserved regression examples pass; all 19 audited closures contain only
the three standard logical axioms. The new direct route has no finite
replay dependency.

## Previous follow-up: decreasing error and both published theta margins (2026-09-23)

The polynomial damping candidate applies Mathlib's existing
`Real.pow_div_factorial_le_exp` twice, at arbitrary natural order. Its
actual-tail consumers reuse the multiplicity-counted summability and
zero-damping power-tail bound, including both signs and every cutoff label.
The actual high-zero region is supplied by the already proved
`xi_zero_gap_initial`, with constant `56`; no sharper region is assumed.

The low block uses the existing exact real reciprocal mass and finite
window expression. Evaluated billion-height bounds and elementary Taylor
inequalities supply all scalar constants for the actual psi averages and
the pointwise reciprocal-logarithmic error. The existing elementary
prime-power correction then gives the published theta lower margin.
Together with the previous constant upper endpoint, both theta margins
hold on the entire ray above `1441000000000`.

The low-height critical-line verification remains an explicit, unproved
input. The global theta assembler additionally needs its finite theta
prefix. No RH-dependent sibling mass evaluation, new zero enumeration,
or replacement axiom is introduced. Prime-counting and short-interval
providers remain unfinished. The existing sibling reuse boundary is
unchanged; these proofs do not reconstruct the zero infrastructure.

The seven new modules and both affected candidate facades compile.
All 50 regression examples pass, and all 21 audited theorem closures
contain only the three standard logical axioms.

## Previous follow-up: evaluated endpoint and critical-strip high tail (2026-09-23)

The full power-tail estimate now specializes the existing BV-derived atom
to gap zero, using the actual proved critical strip. It reuses the existing
complete series and summability; no high-region or turning-point hypothesis
remains for a constant-error endpoint row. The actual uniform psi consumer
retains only the finite low-height gap.

Mathlib's harmonic upper sequence and certified log/pi bounds provide the
new scalar constants. The existing exact real mass is below `0.03`; the
selected reciprocal window and both full power tails have rational bounds.
All endpoint arithmetic is proved, including the strict published theta
upper margin. Actual low-height verification below `10^9` remains explicit
and unproved here. No RH-dependent sibling norm-mass evaluation is used.

All six new modules, candidate facades and 52 regression examples compile;
the 23 audited exported closures contain only the standard three axioms.

## Previous follow-up: exact real mass and full-power low bands (2026-09-23)

The new small-prefix estimate uses the existing unconditional real
reciprocal mass from `ZetaXiHadamardConstant` and `XiLowReciprocalMass`.
It does not use the RH-dependent norm-mass evaluations excluded below.
Same-height reflection supplies the lower real-part gap, and elementary
norm algebra converts each prefix reciprocal norm into a multiple of its
real reciprocal atom. This sharpens the counting-only expression without
any new zero data or sibling import.

The split-low proof reuses the BV-derived height-and-gap atom, the actual
finite band partition, full-tail summability and the proved scalar density
integral. At zero damping the full height power is retained with coefficient
one; no exponent splitting is needed. The actual uniform psi consumers
include cutoff multiplicities, empty bands and both signs. Taking minima
preserves or improves the old endpoint bounds. Actual numerical zero
verification and scalar values remain to be proved.

The refined mass, three new consumers, prior mixed theta consumer and
58 regression examples compile. All 18 audited closures have only the
standard three axioms. No new sibling dependency or low-zero certificate
is introduced.

## Previous follow-up: uniform endpoint estimates (2026-09-23)

The normalized actual psi estimate now holds throughout the ray above
its starting point with a single evaluated endpoint budget. This reuses
the existing BV-derived complex-power decay, actual multiplicity-counted
zero sums, and complete Rosser tail. Increasing damping decreases each
kernel atom and hence the convergent tail. Low-zero and normalized
correction terms also decrease. No new sibling import or zero-counting
argument is needed.

The high-tail norm estimate is factored out before the turning-point
condition is introduced. Its scalar majorant is then evaluated once at
the starting point. The old Rosser API remains unchanged. The two adjacent
averages retain different normalizations, and the conclusion includes
every point on the ray, including prime-power jumps.

The three new modules compile and nineteen exported closures have only
the standard three axioms. This proves the uniformity of an endpoint
estimate, not its final numerical value. Low-height verification, a
suitable quantitative region, scalar bounds and finite prime estimates
remain open. The sibling refresh below remains current.

## Previous follow-up: complete cutoff cover and refreshed sibling boundary (2026-09-23)

The fixed and growing estimates now cover every positive root parameter.
The actual averages select their branches independently and retain the
correct lower normalization. The new direct theta consumer uses the
published relative margins; the stronger internal fourth-power route is
optional, not a replacement for the paper's statements. All five new
modules compile; 37 examples and 27 standard-axiom closure checks pass.
Numerical zero information, uniform scalar bounds, finite prime estimates,
and the three final providers remain unfinished.

Published main refs were checked again. Robin1984 remains
`acab1a31f31e0499518a4416b63281e0b4838f9c` and BV remains
`7a1748306e026825ed6a5555516cc2f28989b2ac`. WIPResearch has advanced
from the revision below to
`10607f234b2e5a64345bd49c7f21f80a419bc818`. The older audit must not
be read as excluding all new reuse opportunities.

The following additions at that exact WIP revision were source-inspected:

| Module under `RobinBV/` | Reusable content | Remaining input |
| --- | --- | --- |
| `Mathlib/Analysis/Complex/ZeroFreeBandBound` | Complex-power bounds retaining height denominators; only Mathlib imports | Real-part gap |
| `Sieve/Proof/BKLNWReciprocalAbel` | Reciprocal Abel identity; only Mathlib imports | Arbitrary natural-bin coefficients |
| `Sieve/Proof/BKLNWReciprocalHeightBound` | Multiplicity-weighted reciprocal-height bound | Finite positive-height band |
| `Sieve/Proof/BKLNWHeightBandDensityAggregation` and `BKLNWHeightBandDensityExplicit` | Endpoint-aware density aggregation and explicit coefficient substitution | A supplied `zero_density_bound`, region and endpoint bounds |
| `Sieve/Proof/FKSDetectorAggregation` | Actual Type-I/Type-II detector counting, including multiplicity copies | Both detector moment bounds; threshold constant is existential |
| `Sieve/Proof/BKLNWClassicalZeroFreeEnvelope` | Uniform finite-height classical region | Constant remains existential |
| `Sieve/Proof/Zeta23ZeroFreeBridge` | Actual logarithm-ninth zero-free estimates | Positive constant remains existential; not Dusart's numerical region |

The updated lakefile pins PNT at
`f8f58c749d6cde8a641348fcd5e4702993651cd6`, an ancestor of our existing
PNT pin, and Zeta23 at `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.
The WIP sources retain Jonas Whidden's Apache-2.0 notices. No new sibling
dependency, checkout, source extraction or build/axiom audit is claimed
for this refresh. Before importing any addition, check its exact closure
and port only the needed proof. Our current fixed/growing cutoff argument
already reuses the established actual-xi counting and Abel infrastructure;
it does not need to re-import equivalent finite-band wrappers.

## Previous follow-up: normalized estimates and explicit smoothing (2026-09-23)

The sharp-tail comparison reuses the previous power-majorant estimate;
it does not rebuild any zero-sum infrastructure. The upper-primitive
parameter condition is proved equivalent to the paper's lower bound on
the root parameter. The entire sharp budget is proved no larger than the
old budget on its stated domain.

Exact power cancellation gives dimensionless bounds for the actual psi
averages and pointwise error. A chosen order-dependent smoothing step
has an order-independent total width, stays in the analytic domain, and
has exact cost `1/(8*log(x)^4)`. Thus the remaining `3/8` scalar allowance
would give the required `1/2` psi coefficient. No low-height location,
numerical region, or final scalar bound is silently supplied here.

All three new modules, modified consumers and the candidate facade
compile. Twenty-one new and twenty-one preserved examples pass; all
twenty-five audited closures have only the three standard axioms. The
fixed-height branch is still needed where the growing-cutoff domain does
not cover the initial range. Final Dusart providers remain unfinished.

## Previous follow-up: sharper density tail (2026-09-23)

The zero-counting, improper-Abel, symmetry and high-box estimates are
reused directly. A new Mathlib-only upper primitive proves the density
coefficient in HDR Lemma 49 by elementary calculus. The reciprocal-height
correction is extracted from the previous power-majorant proof, with its
cutoff cancellation proved independently. No sibling import, RH-based
mass evaluation or new zero enumeration is introduced.

`XiRosserSharpTail` combines these with the actual complete zero tail.
`DusartBoxRosserSharpBudget` supplies the corresponding actual averaged
and pointwise psi estimates. Our counting-envelope constants remain
`log(t)+17`; this is not a claim to have proved the paper's sharper
counting coefficients or final numerical Dusart bounds. The low-height
information, optimized region, uniform scalar inequalities, finite prime
prefix and final providers remain open.

Three new modules and the modified candidate/facade compile. Seventeen
new examples and twenty-six old examples pass. All twenty-three audited
theorem closures have only the three standard axioms.

## Previous follow-up: exponential cutoff parameters (2026-09-23)

The existing kernel, finite window and complete tail are reused unchanged.
The Mathlib-only parameter candidate now chooses the integrable exponent
`p=q-1/nu^2`, proves its exact domain and turning conditions, and evaluates
the selected coefficient and complete integral majorant at `exp(nu*X)`.
It includes the exponential splitting identity of HDR equation (2.24).
No zero-counting, conjugation or improper-Abel infrastructure is rebuilt.

`XiRosserNuWindow` reuses the upper-primitive estimate to obtain the
Lemma-48-style expression with our proved counting envelope.
`XiRosserNuTail` retains the actual whole tail and all cutoff labels.
`DusartBoxRosserNuBudget` discharges the parameter choices in the actual
averaged and pointwise psi estimates. The two adjacent averages can use
different cutoffs at the same `nu`, with coverage transferred monotonically.

There is no new sibling dependency or weakened hypothesis. Strong enough
low-height information, optimized region parameters, the final uniform
scalar inequality, finite prime prefix and final providers remain open.
In particular the present power-majorant coefficient is not identified
with the sharper incomplete-Bessel estimate in HDR Lemma 49.

Four new modules, the adapted candidate and facade, twenty-seven new
examples and twenty-three preserved examples compile. All twenty-eight
audited theorem closures have only the three standard axioms.

## Previous follow-up: increasing-window endpoint estimate (2026-09-23)

Dusart HDR section 2.4, Lemma 48 uses a finite exponent-one density. Its
upper bound now follows directly from an elementary upper primitive,
whose derivative is the density plus a proved nonnegative correction.
This avoids introducing incomplete-Gamma infrastructure. The exponential
cutoff evaluation gives the paper's factor
`exp(-X/nu)*nu^2*(nu*X-log(b))` exactly. The counting envelope remains our
proved `log(t)+17`, not the paper's sharper numerical coefficients.

The actual zero sum uses the existing Rosser window theorem. Both signs
reuse the existing `XiHeightBand` cover: that proof was generalized to
nonnegative conjugation-invariant weights, and its reciprocal-norm API
is preserved unchanged. Halving the lower majorizing-window cutoff keeps
every zero on the band's lower boundary. Equal band cutoffs cost zero.

The box atom uses the already adapted BV complex-power estimate, retaining
height-dependent exponential damping with the exponent-one denominator.
The combined consumer bounds actual averaged and pointwise psi using this
finite band and the previous complete high-tail bound. One arbitrary
region constant controls both blocks. No RH-dependent mass evaluation,
new sibling import or zero enumeration is introduced. Low-height gap,
optimized region and final uniform scalar inputs remain to be proved.

Five new modules, twenty-three new examples and fifteen preserved examples
compile. The candidate facade and combined consumers also compile; all
twenty-five audited theorem closures have only the standard three axioms.

## Previous follow-up: elementary Rosser bounds (2026-09-23)

The actual infinite zero sum and its counting infrastructure are reused
unchanged. `LogDampedMajorant` splits off any real power and selects the
remaining kernel's cutoff value after its turning point, or its global
peak otherwise. `LogPowerTail` proves the exact improper integral with
arbitrary logarithmic offset. `LogDampedBound` bounds both Rosser density
terms and cancels the split powers in the cutoff branch. These candidates
use only Mathlib and the already proved scalar kernel layer.

`XiRosserClosedBounds`, `DusartBoxRosserClosedTail` and
`DusartBoxRosserClosedBudget` connect the elementary expression to the
actual whole tail, averaged psi and pointwise psi. The parameter range is
`1<p<q`, with `q=m+4` in the box estimate; the region constant remains
arbitrary. Integrability is proved, not inferred from a formal integral
identity. Both signs, every cutoff multiplicity, and all correction terms
remain covered by the previous complete-tail theorem.

The six new modules, their candidate facade, thirty-one new examples and
sixteen preserved tail examples compile. All twenty-six new theorem
closures use only the three standard axioms.

The sibling check reconfirmed existing reuse, not a replacement theorem
for the missing numerical constants. Robin/WIP norm-mass evaluations
assume RH; the inspected BV counting bound has an existential constant
for nonprincipal characters. The stronger low-height information,
optimized region, uniform fixed-cutoff scalar bound, finite prime prefix
and three final providers remain to be proved. No new sibling import is
needed for this elementary-integral step.

## Previous follow-up: complete Rosser tail and pointwise psi (2026-09-23)

The infinite step now reuses `XiZeroCountingImproper` and its existing
count-boundary theorem directly. `XiRosserAbel` proves actual damped-kernel
summability and the exact improper Abel identity. The new Mathlib-only
tail/integral candidates prove inverse-square domination and absolute
integrability of both the logarithmic density and reciprocal-height
correction. Neither convergence nor an upper boundary limit is assumed.

`XiRosserTailBound` passes the decreasing window estimate to infinity,
keeping the lower counting discrepancy. `XiRosserCutoff` adds every cutoff
label and combines its multiplicity with that discrepancy before applying
the already proved strict-count envelope. `XiRosserSymmetry` reuses the
existing multiplicity-preserving conjugation to cover both ordinate signs.
The closed absolute-height tail has no leftover multiplicity charge.

`DusartBoxRosserTail` bounds the actual complete high box sum, retaining
the full `m+4` height power. The constant-`56` specialization derives its
region input. `DusartBoxRosserBudget` connects this tail to the actual psi
averages and pointwise error, including all finite blocks, corrections and
the exact smoothing loss. Its stronger low-height and arbitrary-region
inputs remain explicit. A named local instance also fixes an import-name
collision exposed when joining the window and height-band proof branches.

Eight new modules, two adapted consumers, twenty-five new examples and
the twenty-seven preserved window examples compile. Thirty-seven exported
theorem closures use only the standard three axioms. The remaining Rosser
work is quantitative evaluation/majorization of the convergent integrals
and uniform parameter bounds; the actual infinite zero sum is now handled.
The optimized region, sufficiently strong low-height information, finite
prime prefix and three final Dusart providers are still unfinished.

## Newest follow-up: Rosser weighted windows (2026-09-23)

`XiWeightedCountingBounds` directly reuses the exact actual-xi Abel identity
and the proved `log(t)+17` error envelope. Integration by parts retains
the envelope derivative `1/t` and signed endpoint discrepancies. Joining
the two monotonicity branches cancels the discrepancy at the turning
point, leaving twice the envelope times the peak, not four times it.

The Mathlib-only `Pow/LogDamped` and `Pow/LogDampedShape` candidates prove
the derivative, square-root upper bound, continuity and turning-point signs
of `exp(-q*log(t)-a/log(t))`. `XiRosserWindow` applies these to the actual
multiplicity-counted zeros, handling maxima before, inside and after the
window. Equal endpoints have exactly zero cost. This follows the argument
of Dusart HDR section 2.4, Lemma 47, but explicitly uses our proved counting
envelope, not the paper's stronger numerical coefficients.

`DusartBoxRosserWindow` connects the result to actual positive-ordinate
box spectral sums, retaining the full inverse-height exponent `m+4`.
The general theorem keeps the region constant `R` arbitrary and its region
hypothesis explicit. The constant-`56` specialization uses the existing
proved region and requires no zero-location premise. No new sibling import,
RH-dependent mass evaluation, or zero enumeration is introduced.

All six modules and twenty-seven regression examples compile. All twenty-six
exported theorem closures contain only `propext`, `Classical.choice`, and
`Quot.sound`. The improper weighted integral and sharper scalar estimates,
optimized region and sufficient low-height information, finite prime prefix,
and three final providers remain unfinished. This finite-window step is not
yet the complete Rosser high-tail bound or the final Dusart theorem.

## Newest follow-up: the initial low strip is now proved (2026-09-23)

The unconditional real reciprocal mass already available in
`ZetaXiHadamardConstant`, positivity from `XiLowReciprocalMass`, and the
actual multiplicity-preserving reflection exclude all xi zeros with absolute
ordinate at most one. Only Mathlib's elementary bounds `exp(1)<3`, `pi>3`,
and `EulerGamma<2/3` are needed: a single suitably reflected low zero would
exceed the total mass. Robin/WIP's RH-dependent norm-mass identities are
not used or weakened into unconditional claims.

The actual classical zero-free constraint then gives an initial gap on every
bounded strip, with constant `56` and logarithm of the upper cutoff. This
removes the supplied low-height hypothesis from `KadiriInitialMaster` and
provides the low input of the first constant-`56` elementary bootstrap.
It does not provide stronger low-height RH information or the final region.

The complete damped tail now has an explicit two-tail majorant, using
Mathlib's subtype/indicator summation and the already proved closed Lehman
bound. Taking its minimum with the prior estimate gives the actual psi
budget without an unevaluated zero sum. The weak initial bounded gap also
provides an unconditional starting box estimate. Sharp numerical constants
and their full parameter ranges remain to be proved; no new sibling import
or change to the previously reviewed revisions was needed.

Six new modules and twenty-two new examples compile. Twenty-six audited
exports, including the initial master without its old low-zero premise,
use only `propext`, `Classical.choice`, and `Quot.sound`.

## Newest follow-up: fixed low cutoff and damped high tail (2026-09-23)

The existing `xi_zero_gap_initial` is reused directly, not reproved. It
supplies the constant-`56` gap for actual xi zeros above `10^9`. The new
height band uses this region, the earlier multiplicity-preserving
conjugation, and the actual reciprocal-window estimate. The strong gap
input is now confined to one fixed low prefix, while the upper cutoff may
vary with `x`. Equal cutoffs give exactly the previous single-cutoff budget.

The generic averaged-power estimate also retains the real part of the
exponent. `DusartBoxHeightGap` uses this to combine higher-order height
decay with the BV-style exponential gap factor. Its actual-xi specialization
uses the proved initial region. `DusartBoxDampedHighTail` sums that stronger
kernel using the already reused unconditional inverse-square summability.
Thus no new RH-dependent mass or zero-free hypothesis is imported.

This is an intermediate estimate toward Dusart's Rosser--Schoenfeld method
(HDR, section 2.4, equations (2.8)--(2.12)); it is not a claim that the
paper's four-region optimization or final constants are already proved.
The explicit damped-kernel integral, stronger numerical region and uniform
parameter estimates, low-height input, and final providers remain to finish.

All six modules and twenty-five new examples compile. Twenty-five audited
exports use only `propext`, `Classical.choice`, and `Quot.sound`. The sibling
revisions below remain unchanged; this increment reuses their already
adapted infrastructure rather than importing further sibling closures.

## Newest follow-up: low reciprocal-norm mass from counting (2026-09-23)

The norm-mass bound no longer needs an independent numerical assumption.
The new modules directly reuse `sum_xi_height_window_eq_boundary_sub_integral`
and `abs_xiZeroCountingRemainder_le_log_add`. The latter already applies
from height ten. Its explicit envelope divided by `t^2` has a proved
elementary primitive, giving a logarithmic-square bound on the actual
positive-ordinate reciprocal-norm sum.

Existing real-axis nonvanishing, multiplicity-preserving conjugation, and
same-height reflection supply the remaining pieces. Conjugation handles
both ordinate signs; reflection turns the stated upper low-height gap
into a lower one and bounds the small prefix. The resulting
`sum_xi_low_reciprocal_norm_le_explicit` retains every multiplicity and
does not lose endpoint zeros. No RH-dependent mass evaluation is imported.

`DusartBoxCountingBudget` connects this explicit estimate to the actual psi
and fixed theta interfaces. Its remaining low-gap input is **not** proved
by the mass bound. The uniform scalar parameters, finite prefix, and three
final providers remain unfinished. Six new modules and nineteen examples
compile; nineteen audited exports have only the standard three axioms.

## Newest follow-up: corrections and actual pointwise error (2026-09-23)

The complete negative-even correction is now bounded by the geometric
series `1/(2*(x^2-1))`. This uses the existing actual box transform,
Mathlib's negative-exponent monotonicity, local average norm bound, and
geometric summation. It neither assumes a bound on the cutoff derivatives
nor discards low negative-even zeros.

`DusartBoxPsiError` directly reuses
`neg_two_mul_logDeriv_riemannXi_zero_eq` from the pinned PNT
`Mathlib/NumberTheory/LSeries/RiemannXiDivisorZeros.lean`, revision
`f6147e7572ab3abe5428101bc0b13627bcb005df` (Matteo Cipollina, Apache-2.0).
This simplifies the full endpoint constant to `log(2*pi)`. No new
Hadamard-constant proof or RH-dependent evaluation was introduced.

The new budget controls the actual psi averages and, by both adjacent
averages, the pointwise psi error including jumps. The existing
`hasThetaLogFourthError_of_psiLogFourthError_sharp` then transfers a
psi coefficient `1/2` to the required theta coefficient `648/1000`
above `4e18`. All zero and scalar inputs of this transfer remain explicit
in `HasDusartBoxLogFourthBudget`; that proposition is not yet established.

Four new modules, eighteen regression examples, and fourteen exported
axiom closures were checked. All closures use only the standard three
axioms. The remaining low-zero inputs, uniform parameter/scalar proof,
finite prefix, and three final providers still require completion.

## Newest follow-up: complete high-zero tail (2026-09-23)

The quantitative high-height obligation from the earlier sections is now
proved for the actual box weight. Mathlib's existing `fwdDiff`, complex-power
derivative, and FTC give the exact averaged-power identity at every natural
order, with denominator `h^n*s*(s+1)*...*(s+n)`. The resulting norm bound
gains inverse height to power `n+1`. Five reusable candidate modules expose
the local recurrence, primitive identity, and norm estimates.

`DusartBoxHeightDecay` applies these results to the actual paired atoms.
`XiHeightTailZeroHigh` reduces the zero-height inverse-square tail to four
times the existing tail at half the cutoff. `DusartBoxHighTail` then applies
the proved Lehman counting bound for `T>=10^9`. This controls the entire
high-zero series, with multiplicities, both ordinate signs, and zeros
exactly at the cutoff. It does not need RH or an assumed low-zero mass.

`DusartBoxZeroSplit` proves the exact strict-low/closed-high decomposition
and combines that high bound with the previously adapted BV finite-gap
bound. The low-gap and reciprocal-norm mass inputs remain explicit: this
does not establish the missing numerical low-height facts or the final
Dusart providers. The negative-even correction budget and fixed-cutoff
scalar certification also remain to be completed.

All nine new modules compile. Eighteen new regression examples pass;
twenty-eight audited exports use only `propext`, `Classical.choice`, and
`Quot.sound`. CI builds the candidates and consumers serially before tests.
The sibling audit below remains authoritative; no broader sibling import
or RH-dependent evaluation was added for this increment.

Previous follow-up (2026-09-22): BV's generic power-decay leaf has now been
adapted and connected to the actual Dusart box atoms and finite xi sums.
The exact averaged-power identity and absolute summability also reuse the
existing paired explicit-formula infrastructure. Details follow here;
older sections retain the obligations as they stood at each increment.

## Complex-power bound and actual box-transform follow-up

The reviewed BV file `Helpers/ComplexAnalysis/CpowDecayBound.lean`, at
`7a1748306e026825ed6a5555516cc2f28989b2ac`, proves
`BombieriVinogradov.ComplexAnalysis.norm_real_cpow_div_le_exp_gap_mul_reciprocal`
using only Mathlib. Its hypotheses are `1<=y` and `Re(s)<=1-delta`;
there is no RH, character, or assumed zero-free-region theorem in this
leaf. The proof is adapted under namespace `Complex` in the new
`Mathlib/Analysis/SpecialFunctions/Pow/ComplexDecay.lean` candidate.
Its exact source, licence, original name, and renaming are recorded there.

`DusartBoxZeroBounds` now applies that inequality to every point in the
actual averaging support. `DusartBoxSpectralFormula` sums it over arbitrary
finite selections of the actual xi divisor, preserving multiplicities.
The coefficient is `(x+(m+3)*h)*exp(-delta*log(x))`, with the reciprocal
norm sum kept explicit. This adapts BV's finite-sum assembly without
importing its nonprincipal-character or existential-constant interfaces.

The new primitive-transform identities use Mathlib's Fubini, substitution,
FTC, and complex-power derivative directly. They prove
`F_w(-s)+1/s=average(t^s/s)` and its exact exponent-one main term.
The existing `summable_smoothedXiPaired` proves absolute convergence of
these actual averaged powers. The new full psi spectral formula therefore
does not rebuild contour integration, Hadamard factorization, or zero
enumeration, and never splits a divergent unpaired reciprocal series.

Still needed: quantitative high-height decay and tails, the negative-even
correction estimate, actual low-height zero information, and fixed-cutoff
scalar certification. The RH-dependent Robin/WIP mass evaluations remain
inapplicable as unconditional numerical bounds. This increment does not
finish the three Dusart providers or the all-`k` classification.

The ten new modules compile in the pinned Lean 4.34 environment. Nineteen
new regression examples and five preserved explicit-formula examples pass.
All twenty-six audited new exports have only `propext`, `Classical.choice`,
and `Quot.sound` in their closures. No RH-dependent mass evaluation is in
the new theorem statements or axiom closures.

Current follow-up: the unconditional high counting envelope, closed
Lehman tail, pole estimates, and explicit smoothed Gamma bounds are proved
and connected to the master inequality; see the final sections. Earlier sections record
the obligations at each increment and are superseded where explicitly noted.

This focused source review was performed on 2026-09-22 before extending the
same-height, multiplicity-counted xi pairing. It is not a claim that no other
useful sibling theorem exists. Check this record before repeating discovery.

## Published revisions inspected

| Repository | Exact revision | Toolchain | Licence |
| --- | --- | --- | --- |
| Robin1984 | `acab1a31f31e0499518a4416b63281e0b4838f9c` | Lean 4.33.1 | Apache-2.0 |
| bombieri-vinogradov | `7a1748306e026825ed6a5555516cc2f28989b2ac` | Lean 4.33.1 | Apache-2.0 |
| WIPResearch | `bdc46941c4f2e13fb84e0a338b905bb10e711357` | Lean 4.33.1 | Apache-2.0 |
| PNT dependency | `f6147e7572ab3abe5428101bc0b13627bcb005df` | Lean 4.33.1 | Apache-2.0 |

The first three were resolved from their published main branches; the last
is the locked dependency. No additional checkout or worktree was created.
Project declarations are checked here with Lean 4.34.0.

## Directly reusable analytic-order proof

BV's [AnalyticOrderConjugation](https://github.com/kimihiro64/bombieri-vinogradov/blob/7a1748306e026825ed6a5555516cc2f28989b2ac/BombieriVinogradov/Helpers/ComplexAnalysis/AnalyticOrderConjugation.lean)
contains `ComplexAnalysis.AnalyticAt.conj_conj`,
`analyticOrderAt_conj_conj`, and `analyticOrderNatAt_conj_conj`.
These are general complex-analysis statements, with only local analyticity
as a hypothesis. Its direct imports are Mathlib modules; its private
derivative helper and three public proofs have explicit proof bodies.

The pinned PNT [KadiriZeroCounting](https://github.com/kimihiro64/PrimeNumberTheoremAnd/blob/f6147e7572ab3abe5428101bc0b13627bcb005df/PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean)
also has the private `Kadiri.analyticAt_conj_conj` and
`Kadiri.analyticOrderAt_conj_conj` proofs. The surrounding zero-counting
results have additional hypotheses; those are not imported by the extraction.

Their local-factorization argument is reused in
`Mathlib/Analysis/Analytic/Order/Conjugation.lean`, under the `Complex`
namespace. Its only imports are Mathlib's analytic order, complex Cauchy
integral, and derivative-star modules. Mathlib's existing
`differentiableAt_conj_conj_iff` replaces the older derivative helper.
The candidate records both sources and renamings, and is built independently
before its xi consumer. No zero-free region or RH premise is added.

## Other inspected source and applicability

| Source | What is already proved | Applicability here |
| --- | --- | --- |
| BV `Helpers/ComplexAnalysis/DivisorIndexTransport` | Existence of an index at equal multiplicity, carrying a `Fin.cast` label | Useful transport pattern; not itself an equivalence under `ρ -> 1-conj(ρ)` |
| BV `ZeroFree/QuadraticConjugateZeroIndex` | Existence of a conjugate zero index for a primitive quadratic character | Does not establish a bijection preserving every multiplicity label |
| BV `ZeroFree/PairSubtypeTsum` | Exact sum over two distinct indices | Applicable when retaining a distinguished pair; currently no extraction needed for the whole-series reindexing |
| BV `ZeroFree/RiemannXiZeroSumPositivity` | Nonnegativity of the xi logarithmic-derivative series for `Re(s)>1` | Not the compact smoothed comparison for `1/2<σ<=1`; preserve its domain |
| Robin `NicolasLandau/WeightedZeroPairing` | Exact weighted zero atoms and a vertical resolvent estimate | Existing project contour/transform infrastructure already adapts the Robin route |
| Robin `NicolasLandau/XiZeroConstant` | Inverse-square summability and an exact xi mass under RH | Reuse the unconditional summability leaf; do not import the RH-dependent mass evaluation as unconditional |
| WIP `NumberField/Proof/PairedDirichletZeroIndex` | Value-preserving equivalence between a product divisor and two factor divisors | Reuses sigma/fiber/subtype equivalences; its carrier is a Dirichlet product, not this xi reflection |
| WIP `NumberField/Proof/QuadraticLZeroSymmetry` | Reflection of primitive quadratic L-zeros | Different carrier; the xi function-level reflection/conjugation is already proved here |
| WIP `NumberField/Proof/RiemannShiftedZeroMass` | Exact shifted xi mass and bounds under RH | Cannot supply the unconditional Dusart tail estimate without discharging RH |

BV paths abbreviated `ZeroFree/...` are under
`BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/`. WIP paths start at
`RobinBV/`. The modules in this table were source-inspected, not wholesale
added as dependencies or claimed to have been rebuilt here. Further reuse
requires checking the particular declaration's full closure and axioms.

## Project-specific assembly now implemented

The existing `ZetaXiStechkin.riemannXi_conj` and
`ZetaXiDivisorReflection` already provide xi function conjugation and
the multiplicity-preserving map `ρ -> 1-ρ`. The extracted order theorem
supplies the conjugate multiplicity equality. `ZetaXiDivisorConjugation`
combines these into a same-height equivalence preserving the finite label.

Whole-series and reflection-stable-subtype pairing uses Mathlib's
`Equiv.tsum_eq`, `Summable.comp_injective`, `Summable.subtype`, and
`Summable.tsum_subtype_add_tsum_subtype_compl`. These do not need reproof.
`KadiriZeroSummability` instantiates the already-proved smoothed summability
theorem with the actual paper weight. The resulting central-strip
elimination leaves the outer-strip series explicit; quantitative outer-zero
and gamma bounds remain required for Dusart's unconditional constants.

For retaining one distinguished off-critical pair, the new general lemma
`Summable.pair_le_tsum_of_involution` applies Mathlib's existing
`Summable.sum_le_tsum` to the symmetrized series and reindexes it. Individual
summands may be negative. The nonfixed-orbit hypothesis prevents counting a
critical-line zero twice. `ZetaXiDivisorPairing` and `KadiriZeroSums` apply
this to the actual divisor, retaining the complete outer-strip remainder.
`KadiriOuterMaster` also integrates central-strip elimination into the
paper-weight master inequality. The later `KadiriRetainedZeros` and
`KadiriRetainedMaster` retain one pair at the selected harmonic.
`KadiriRetainedBounds` proves equation (34) directly using monotonicity and
the existing cubic transform bound, and `KadiriDistinguishedZero` inserts
that quantitative estimate into the actual master. These symbolic results
do not certify the remaining numerical zero-free-region constants.

## Verification and remaining boundary

The later `XiHeightTail` layer also reuses
`SmoothedXiRemainder.summable_xi_divisor_shift_inv_sq`, ultimately the
unconditional PNT xi inverse-square theorem, rather than the RH-dependent
mass evaluations. A bounded-strip comparison proves summability of the
actual Mossinghoff--Trudgian absolute-height tail. `KadiriOuterPairs`,
`KadiriOuterTail`, and `KadiriTailMaster` then assemble the weighted error
with the existing reflection and retained-zero machinery. The numerical
tail estimate and the proof of absolute-height separation remain open;
neither follows merely from this reuse of summability.

The subsequent `XiHeightTailPairing` reuses the same actual conjugation
equivalence to obtain the positive-ordinate formula. `XiLowReciprocalMass`
and `XiHeightTailZero` instead use the project's independently established
unconditional real Hadamard constant and the locally finite divisor to
bound the height-zero tail by a finite reciprocal-mass subtraction. This
does not use the RH-dependent sibling evaluations. The finite low-zero
lower sum and the numerical tail budget still require verification.

Both general candidates, their xi consumers, actual-weight summability,
zero sums, and outer master compile against the pinned project environment.
The 28 declarations audited by `.research/DusartXiPairingAxioms.lean` use
only `propext`, `Classical.choice`, and `Quot.sound`. The Lean regression
`test/lean/KadiriZeroSums.lean` passes, including negative individual
summands, infinite analytic order, fixed critical-line labels, preserved
multiplicity labels, and the actual retained-pair sum. CI builds these
modules serially in `lean-foundations`, before certificate jobs.

Still required: outer-zero, pole, and gamma estimates, the numerical parameters giving
`R=5.573412`, and the remaining unconditional PNT/finite analytic inputs.
This reuse increment does not finish the three final Dusart providers or
the all-`k` theorem.

## Counting-to-integral follow-up

The additional BV leaf `ExplicitFormula/Horizontal/ZeroHeightWindowCountBound`
proves a logarithmic window bound, but for nonprincipal primitive characters
and with an existential constant. It is not the numerical zeta counting
estimate required here. PNT's `Backlund/ZeroCountCrude` proves an
unconditional `|N(T)| <= A*T^(3/2)` bound with existential `A`, which supports
convergence. `IEANTN/KadiriZeroCounting` explicitly distinguishes that route
from its conditional, sharper Backlund-constant route.

Mathlib's existing Abel formula and Robin's prime-log application use
natural locations. The new Mathlib-only `MeasureTheory.Integral.FinsetAbel`
instead integrates each atom's indicator using the existing FTC to obtain
the finite identity at arbitrary real heights. `XiZeroCountingAbel` applies
it to the already-established actual divisor and local finiteness, not to
a newly assumed enumeration. `XiZeroCountingRemainder` subtracts the smooth
main term exactly. These are analytic identities, not a replacement claim
that the quantitative counting error has been proved.

For the subsequent infinite passage, no new zero-count growth theorem is
needed. `InfiniteSum.Sublevel` uses Mathlib's dominated convergence for
series to derive the vanishing counting boundary directly from the
already-proved summability and decreasing kernel. `XiZeroCountingImproper`
then proves genuine improper integrability from the finite identity.
`XiLehmanAbel` specializes this unconditionally to the actual xi pair,
including the closed-cutoff atom. The explicit counting discrepancy bound
is still required for numerical control, not for this convergence step.

`XiLehmanSmoothTerm` and `XiLehmanRemainder` now complete smooth subtraction
and the infinite discrepancy identity. Their quantitative tail estimate
explicitly requires the actual bound `|R(x)|<=2log(x)`; this is not supplied
by the inspected sibling counting results. The 21 exports in this increment
were built and audited with only the three standard logical axioms.

There is a further endpoint distinction when reusing PNT's counting API:
at the pinned revision, `IEANTN/ZetaDefinitions.lean` defines
`riemannZeta.N T` using `Set.Ioo 0 T`, while this project's `xiZeroCount T`
uses `0<gamma<=T`. A bridge requires the full cutoff multiplicity or an
explicit right-limit argument, as well as conversion of the `7/8` offset.
No equality of these two counting functions at zero heights is claimed.

The endpoint bridge is now implemented in `XiZeroCountingEndpoints` and
`XiZetaCountingBridge`: strict xi counts equal PNT's `N(T)`; closed counts
add the entire cutoff multiplicity and are right-hand limits of `N`.
`ZetaXiMultiplicity` proves that the xi divisor weight equals PNT's integer
zeta order. The finite grouping reuses
`Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt`
from the pinned `Mathlib/Analysis/Complex/DivisorFiber` module. Its original
authorship and licence remain in the dependency. The bridge needs neither
the RH-dependent mass formulas nor the `KadiriZeroCounting` import.

`XiZetaCountingBounds` now also converts the `7/8` offset explicitly.
Under the stated RvM hypothesis, its constants give the `2log(T)` envelope
for `T>=2, log(T)>=5`, and then the actual Lehman bound. The hypothesis is
still open. All 21 public results in this increment build and have only
`propext`, `Classical.choice`, and `Quot.sound` in their axiom closures.

## Backlund auxiliary reuse

`BacklundAuxiliary` now imports the pinned `Backlund/ZeroCountCrude` directly
and uses its `zetaSurrogate` and `zetaSurrogate_differentiable`, including the
residue patch at one. The attribution to Robby Sneiderman and the full pinned
revision are in the consumer. Its differentiability axiom audit has only the
three standard logical axioms. The new symmetrized-power real-part identities
therefore extend an existing entire-function proof rather than reconstruct it.

`BacklundJensen` likewise applies Mathlib's existing `sum_divisor_le`; the new
compactness recurrence and finite-cardinality comparison supply the missing
interfaces for the real crossings. `BacklundRealZeros` proves the actual
crossing bound at arbitrarily large powers. This does not claim that the
coarse PNT growth estimate supplies the explicit logarithmic discrepancy:
argument variation, the counting identity, and sharp enough magnitude and
gamma estimates remain separate proof obligations.

The horizontal comparison is now completed in `BacklundArgument` and
`BacklundArgumentIntegral`. These reuse Mathlib's intermediate value theorem,
integer interval cardinality, exponential covering, continuous-map lifting,
inverse differentiation, and FTC. The new glue proves the actual endpoint
phase bound and its logarithmic-derivative integral form; it does not rebuild
those underlying topological and analytic tools. Its remaining explicit
circle magnitude hypotheses are not presented as a proved sharp count bound.

## Actual rectangle counting and gamma separation

The pinned PNT `RectangleArgumentPrinciple` now supplies the actual residue
calculation. Its `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`,
companion argument-change theorem, and logarithmic-derivative residue
theorem compile and have only the three standard logical axioms. The
project uses the integral theorem directly: `XiCountingRectangle` identifies
its support and weights with the existing zeta count. It does not assume
the companion theorem's separate `hargumentChange` premise.

For the real boundary, Robin's published
`Robin1984.Mathlib.NumberTheory.LSeries.RiemannZetaReal` proves nonvanishing
on the whole positive real axis through its Euler remainder and moment
generating continuation. This project's already-pinned Abel continuation
gives the needed negativity on `[1/2,1)` directly; xi reflection supplies
the rest. `ZetaXiRealNonvanishing` therefore reuses that existing continuation
instead of extracting Robin's much larger independent continuation closure.

`XiHalfContour` reuses the existing xi functional and conjugation identities
and Mathlib's exact interval substitution/conjugation theorems. The existing
gamma-product differentiation is generalized in place to the nonvanishing
right half-plane, retaining its old export unchanged; `BacklundXiLogDerivative`
then reuses it to connect the actual counting integrand to the surrogate.
`XiCountingDecomposition` uses PNT's existing `continuousAt_digamma_of_re_pos`
to justify integrability, splits both contour segments, and applies the
earlier horizontal Jensen estimate to the actual count. The sharp integrated
gamma, vertical surrogate, and circle magnitude estimates are still required.

## Euler logarithm and vertical-argument follow-up

The vertical argument no longer needs an estimate. The Mathlib-only
`RiemannZetaEulerLog` candidate directly uses
`riemannZeta_eulerProduct_exp_log`,
`DirichletCharacter.eulerProduct_log_eq_LSeries`, and `LSeries_hasDerivAt`.
The required coefficient comparison is just `vonMangoldt_le_log`.
No Euler product or Dirichlet-series differentiation is reconstructed.
The positive-coefficient norm comparison follows the same Mathlib-series
argument already used by the project's `ZetaTrigonometric` candidate.

`BacklundVerticalArgument` uses this analytic logarithm to obtain the exact
vertical integral and its height-independent argument bound, as well as
the centre lower bound. `BacklundCountingEstimate` combines them with the
previous actual contour, Jensen bound, and real-axis Abel estimate.
The 21 new theorems compile and have only the three standard logical axioms.
Sharp integrated gamma and explicit circle bounds are still needed for the
numerical counting error; the all-`k` theorem is not yet established.

## Gamma branch and uniform phase follow-up

The sharp gamma contribution is now proved. `GammaLogBranch` directly
imports the pinned PNT `DigammaSeries` module and reuses its `logGammaSeq`,
`cauchySeq_logGammaSeq`, `exp_logGammaSeq`, packet norm majorant, summable
majorant, and `hasSum_digamma_of_re_pos`. The derivative-of-limit argument
was previously local to the last theorem. Only that portion is adapted
and exported here; Robby Sneiderman's copyright and Apache-2.0 attribution
are preserved alongside the exact revision. The exponential identity and
positive-real phase fix the branch used in the contour, rather than
identifying it with a potentially discontinuous principal Gamma logarithm.

The required quantitative remainder is new: the generic complex trapezoid
identity follows from Mathlib's FTC, and its logarithm specialization has
telescoping norm bound `1/(8*Re z)`. Mathlib's existing
`Complex.tendsto_nat_mul_log_one_add_of_tendsto` supplies the far-endpoint
limit. No real Stirling constant or new Gamma convergence theorem is needed.
Robin's real `robin_log_step_trapezoid` and BV's Fourier trapezoid cutoff
do not state this complex second-derivative remainder. The PNT theorem
`stirling_bound_re_ge_zero` controls Gamma's norm with an existential
growth constant, not the branch's uniformly bounded phase error.

The new branch, phase, exact gamma contours, and actual main-term counting
estimate compile. All 26 theorem closures have only the three standard
logical axioms. The numerical circle estimates remain open; the resulting
counting theorem explicitly retains those hypotheses and does not yet
establish the final numerical zero-free region or the all-`k` result.

## Unconditional high counting and exact closed-cutoff tail

`BacklundCircleBounds` directly reuses the pinned PNT `Zeta0EqZeta` and
`ZetaBnd_aux1b` at `N=1`. These supply an actual Euler remainder on `Re(s)>0`;
the leftmost circle point is `Re(s)=1/10`, so the proof does not incorrectly
apply the other Abel continuation's strict `Re(s)>1/10` hypothesis there.
The right semicircle reuses the already-proved Euler logarithm comparison.
No new Euler continuation or zeta surrogate is reconstructed.

The new mean-value Jensen candidate adapts Mathlib's proved divisor-mass
comparison, with its original attribution and exact pinned revision.
Antipodal averaging uses Mathlib's existing radius-negation invariance.
The resulting circle estimate feeds the existing power-limit argument and
the already-proved actual counting and Gamma contours. It proves the
unconditional `log(T)+17` counting error for `T>=10` and hence `2log(T)`
for `T>=10^9`, not merely an existential growth estimate.

Both count conventions are controlled at arbitrary cutoffs. The new
left-limit transfer bounds the strict count, while the previous right-limit
transfer bounds the closed count. In the exact infinite Abel identity, the
closed-cutoff atom and closed boundary count combine into the strict count.
`xiHeightTail_le_main_add_correction_high` in `XiLehmanHigh` therefore has no
residual cutoff-multiplicity term and no assumed counting envelope.
The module's declarations are in namespace `PrimeFactorUnimodality`.

All 32 new theorems and the preserved horizontal Jensen export were built
and audited with only the three standard logical axioms. The new regression
also checks every positive natural harmonic at the paper's high cutoff.
The zero-harmonic finite mass, outer-zero separation, separate smoothed
pole/Gamma errors, and final numerical zero-free parameters remain open;
this does not finish the three Dusart providers or the all-`k` theorem.

## Weighted master and pole-bound follow-up

The same actual conjugation pairing now proves evenness of `xiHeightTail`,
including transport between the two subtype predicates; no new zero
symmetry is proved from scratch. `XiLehmanBudget` uses the existing exact
integral evaluation and correction bound for nonzero heights, and the
existing unconditional low-reciprocal-mass subtraction at height zero.
Every natural harmonic is covered, not only a fixed finite list.

`KadiriPoleBounds` directly uses
`abs_re_kadiriWeight_laplace_sub_pole_le_mass_im` and the existing
`KadiriLaplacePositivity.re_kadiriWeight_laplace_nonneg`. The latter applies
at complex points throughout the closed right half-plane: it removes the
entire shifted transform, giving the sharper error `eta^2*M(z,theta)/y^2`
without a shifted cubic loss. The new work is the unshifted rational pole's
sign comparison and weighted assembly. It does not rederive integration by
parts, correlation positivity, or the kernel's derivative bound. The
combined master replaces both the pole terms and infinite zero tails.

The separate smoothed Gamma estimates are not implied by the counting
Gamma-phase theorem. They, the separation argument, finite low-zero
numerics, and final numerical zero-free parameters remain required.

## Explicit smoothed Gamma follow-up

`DigammaEulerBounds` directly applies the pinned PNT declarations
`sum_eq_integral_add_integral_deriv` and `abs_B1_le_half`, with
`f(x)=1/(z+x)`. Its derivative integral telescopes, giving the uniform
finite bound `1/Re(z)`. `DigammaLogBounds` then uses PNT's actual
`hasSum_digamma_of_re_pos`, Mathlib's harmonic-minus-log limit, and the
extended Mathlib-only `LogShiftLimit` candidate. The result is the
two-sided complex estimate `norm(digamma(z)-log(z))<=1/Re(z)`.

The inspected BV Gamma-growth leaves and PNT norm-growth estimates use
existential constants; they do not supply this explicit two-sided error.
The new proof nevertheless reuses their underlying proved PNT digamma
series rather than reconstructing Gamma or its convergence. The positive
real shift increases the norm and decreases the reciprocal error, so the
shifted Gamma bound retains the required leading coefficient `1-kappa`.

For the separate smoothed remainder, `SmoothedGammaBounds` reuses
`smoothedGammaRemainder_eq_neg_trivialZeroSum` and the existing twofold
integration-by-parts estimate. PNT's inverse-square summability and tail
bound sum the resulting majorant. The actual Kadiri derivative bound
supplies its cubic constant. There is no new contour interchange,
summability premise, or Gamma convergence assumption.

`KadiriExplicitMaster` inserts both estimates into the actual weighted
inequality, including the zero harmonic and arbitrary finite degree.
All 13 new theorem closures and both reused Euler--Maclaurin inputs were
audited with only `propext`, `Classical.choice`, and `Quot.sound`.
Outer-zero separation, finite low-zero numerics, the remaining parameter
budget, and the final Dusart providers are not discharged by this step.

## Initial numerical region and separation

The existing `xi_zero_three_four_one_constraint` now yields an actual
initial numerical region, not merely an inequality awaiting optimization.
`ZetaZeroFreeInitial` uses Mathlib's Euler-constant and logarithm bounds to
bound its remainder by `4*log(abs(t))` for `abs(t)>=10^9`. Substituting
`sigma=1+1/(8*log(abs(t)))` proves the gap `1/(56*log(abs(t)))`.
The inspected sibling results with unspecified constants are not imported
as a substitute for this numerical starting bound.

`KadiriOuterSeparation` reuses the actual same-height divisor reflection
and logarithmic monotonicity to derive the cutoff condition for every
finite set of harmonics. `KadiriInitialMaster` connects it to the actual
smoothed inequality, also deriving the distinguished zero's upper strip
bound. Only the low-height upper bound below `10^9` remains as a separate
zero-location premise. The general separation lemma supports replacing
the initial constant by subsequent proved improvements.

All eight exports compile and their axiom closures contain only
`propext`, `Classical.choice`, and `Quot.sound`. The seven regression
examples include both signs, the exact high cutoff, and arbitrary degree.

The [Mossinghoff--Trudgian paper](https://arxiv.org/pdf/1410.3926),
sections 2--3, requires an established region and low-height information
before its numerical iterations. Its final iterations start at `5.7`.
Our proved starting constant `56` is not that input and is not the desired
`5.573412`: the intervening improvements and complete numerical budget
must still be proved. No RH verification or final provider is claimed here.

## Exact transform gap and bootstrap normalization

`KadiriTransformGap` directly reuses the project's existing
`kadiriWeight_laplace_eq_rescale` and `re_finiteLaplace_ofReal`. The result
is the paper's exact integral `K(w,theta)`, not a newly assumed transform
identity. Mathlib's finite-sum erase identity extracts the unique zero
natural frequency without dropping its pole contribution.

`KadiriGammaBudget` separates the nonzero frequencies' leading logarithm
from the explicit residual, whose height monotonicity follows from the
existing logarithm and reciprocal comparisons. The complete budget is
then normalized into its leading term and a cubic-scale correction by
exact algebra, retaining the actual derivative mass and low-zero subtraction.

The general region master reuses `kadiri_outer_separation_of_region` for
successive established constants. The preserved constant-56 specialization
supplies its high-height premise from `xi_zero_gap_initial`. The new actual
bootstrap theorem invokes this master before applying the transform and
budget identities; it does not assume the master inequality. Numerical
margin verification, low-height inputs, and final provider construction
are still required. No global monotonicity of the signed `K` integrand or
nonpositivity of the entire correction is asserted without proof.

All 14 new exports and the preserved initial master compile and were
audited with only `propext`, `Classical.choice`, and `Quot.sound`.
The 12 regression examples include the zero-only set and arbitrary degree.

## Height-decaying Gamma follow-up

`DigammaEulerIdentity` factors the existing exact application of PNT's
`sum_eq_integral_add_integral_deriv`; both error bounds now share it.
`DigammaHeightBounds` bounds its derivative integral using
`norm(z+x)^2 >= (norm(z)+x)^2/2` on the right half-plane, then applies
the already-proved digamma limit. This gives the explicit error
`2/norm(z)`, reusing the same actual Gamma series and Bernoulli bound.
The prior `1/Re(z)` estimate remains available unchanged.

The actual shifted Gamma majorant now takes the better error at nonzero
height, with `2*(1+kappa)/abs(t)` as an explicit height bound. The zero
harmonic keeps its previous bound. `KadiriGammaBudget` carries these
individual errors through its exact logarithmic decomposition, residual
monotonicity, and the existing normalized actual bootstrap. No assumed
numerical zero-free region or new Gamma series is introduced by this step.

The new leaves and actual bootstrap compile; 24 audited exports use only
the three standard logical axioms. The height-error, updated bootstrap,
and preserved Gamma and initial-region regressions pass. This does not
verify the target numerical margins or finish the final Dusart providers.

## Exact transform evaluation and interval margins

The finite transform does not require a new integration theory. The
Mathlib-only `ExpLinear` candidate directly uses Mathlib's existing
`integral_exp_mul_complex` for the unweighted term. An explicit primitive
and the existing FTC handle the linear weight, including its zero-exponent
case. `ExpTrig` takes real and imaginary parts using Mathlib's integral
projections and complex arithmetic to obtain purely real endpoint formulas.

`KadiriKernelNormalForm` applies the existing sine addition formulas to
the actual kernel. `KadiriTransformClosedForm` integrates that identity
term by term, producing the exact signed `K`, not a new assumed or
approximate transform. `KadiriTransformBounds` then uses the already-proved
`kadiriKernel_nonneg` and integral comparison to obtain uniform endpoint
bounds. It does not reprove correlation positivity or assert monotonicity
of the signed difference. The actual bootstrap consumes these bounds via
`xi_zero_gap_of_endpoint_bootstrap_margin`; numerical margins remain open.

The independent candidates and actual bootstrap compile, with all 24
audited exports using only the three standard logical axioms. The 20 new
endpoint/transform examples and 14 preserved bootstrap examples pass.

## Uniform complete correction follow-up

The new affine tail bound uses the already-proved `xiLehmanHighBound` and
elementary logarithm and reciprocal comparisons. It retains logarithmic
growth at nonzero heights and exact finite low-mass subtraction at zero.
Nonnegativity of the latter comes from `xiHeightTail_nonneg` and the
existing actual Lehman bound, not an RH-dependent mass formula.

The complete correction now directly applies
`kadiriDerivativeMass_le_majorant` and
`kadiriDerivativeMassMajorant_le_of_moment_bounds`; the moments and their
underlying analytic comparison are not reconstructed. Proved pole and
Gamma monotonicity replace their moving parameters by a fixed corner.
The signed linear term remains in the cubic envelope. The actual bootstrap
derives the upper scale-log bound from failure of its target gap and then
uses a verified maximum-scale budget, rather than assuming global
correction nonpositivity. The numerical inputs remain explicit obligations.

The actual bootstrap and all five envelope modules compile. The 20 new
examples and 65 preserved analytic examples pass; all 20 audited theorem
closures use only the three standard logical axioms.

## Exact polynomial and uniform parameter follow-up

The source of the polynomial construction is Mossinghoff--Trudgian,
[arXiv:1410.3926](https://arxiv.org/pdf/1410.3926), section 5 and table 5.
The new `Trigonometric.Autocorrelation` candidate uses Mathlib's finite
sum multiplication, trigonometric subtraction, and frequency regrouping;
the focused sibling checks did not supply this exact cosine-coefficient
identity. The published generating decimals are treated as exact rationals,
and their cosine coefficients are recomputed, not identified with another
rounded column. The proof covers every phase, with signed input sequences.

`Log.AffineRatio` uses logarithmic monotonicity and elementary reciprocal
comparison. Its uniform parameter consumer and the actual region theorem
reuse the existing bootstrap and divisor conjugation; no zero indexing,
reflection, or numerical region is reconstructed or silently assumed.
The final numerical admissibility and low-height obligations remain open.

Both Mathlib-only candidates and the actual uniform bootstrap compile.
The actual band-budget variant also retains the negative correction,
using monotonicity of the normalized cubic and the existing moment bound.
Its small-scale companion derives the higher height from the previous
region. No monotonicity of the signed transform or the unnormalized
correction is silently assumed. The 20 polynomial/parameter examples and
34 preserved moment/bootstrap examples pass; all 26 audited new exports
have only the three standard logical axioms in their theorem closures.

## Single-crossing and split-bootstrap follow-up

`FiniteLaplace.SingleCrossing` directly applies the existing
`hasDerivAt_finiteLaplace`, `HasDerivAt.real_of_complex`, and
`re_finiteLaplace_ofReal`; no parametric integration proof is reconstructed.
Exponential reweighting of a source with one positive-to-negative crossing
shows that derivative nonpositivity persists. The small generic endpoint
lemma uses Mathlib's proved mean-value monotonicity theorems. Focused
Mathlib and sibling candidate searches did not supply this exact signed
transform endpoint-minimum interface.

The actual Kadiri source crosses at `log(a1/a0)`, so its interval lower
bound is the smaller of two whole-transform values. The actual split
bootstrap reuses the existing scale, higher-height, negative-correction,
and divisor-conjugation proofs. The 13 audited theorem closures contain
only the standard logical axioms; 13 new and 74 preserved analytic examples
pass. Numerical iteration and low-height inputs remain unproved here.

## Real-axis Gamma improvement

The sharper `Re(digamma(x))<=log(x)` bound does not require another Gamma
series proof. `DigammaRealBounds` applies Mathlib's
`AntitoneOn.integral_le_sum` and `integral_inv_of_pos`, then the existing
`tendsto_sum_inv_add_sub_log` and fixed-shift logarithm limit. The PNT
series at the pinned revision remains the analytic foundation.

`SmoothedGammaRealBounds` combines this upper bound with the existing
lower logarithmic error at the shifted argument. Only the coefficient
`kappa` remains in the zero-height error. `SmoothedGammaFactorBounds`
uses that theorem in its actual majorant; `KadiriGammaBudget` and the
complete moment correction inherit the improvement. No zero-counting,
conjugation, summability, or assumed zero-free-region input is reintroduced.

Both new leaves and the complete explicit, uniform, and split bootstrap
consumers compile. All 110 examples in the eight affected analytic
regression modules pass. The 14 audited exports, including the actual
region theorems, use only `propext`, `Classical.choice`, and `Quot.sound`.

## Arbitrary scale covers and grid specialization

`KadiriScaleCoverBootstrap` factors out the actual zero argument from the
two-regime theorem. The previous theorem now specializes that proof to a
Boolean-indexed family. The general theorem accepts any covering family,
retaining both the improved height and the negative correction per band.

For a uniform grid, `KadiriGridBootstrap` directly reuses Mathlib's
`Monotone.biUnion_Ico_Ioc_map_succ` from `Order/SuccPred/IntervalSucc`.
No floor, ceiling, or interval-union infrastructure is reconstructed.
Every positive band count is allowed, and the normalized correction weight
is exactly `j/m`. Numerical margins and low-height zero inputs remain
explicit hypotheses; the grid assembler alone is not a numerical region.

The cover, grid, and preserved two-band theorem compile with only the
three standard logical axioms. The thirteen existing transform regressions
and the new sixteen-band actual-region interface regression pass.

## Elementary budget and derivative-moment substitution

`KadiriConservativeBudget` directly uses Mathlib's proved
`Real.eulerMascheroniConstant_lt_two_thirds` and the project's existing
`re_xi_divisor_reciprocal_nonneg`. No new Euler-constant series or numerical
zero-mass evaluation is needed. Monotonicity of the quadratic and cubic
tail terms propagates this upper bound through the complete correction.
The conservative grid theorem then invokes the actual grid bootstrap;
it retains the low-height zero-location hypothesis unchanged.

`KadiriElementaryMoments` reuses `abs_kadiriKernel₂_le_neg_zero`, proved
earlier using autocorrelation, and Mathlib's `integral_pow`. This yields
the full-support monomial upper bound at every natural degree. Its actual
bootstrap consumer supplies all four required moment bounds directly,
eliminating separate quadrature obligations without a sampled maximum.

All four modules compile. Eleven audited declarations, including the
Mathlib Euler bound and the actual elementary region theorem, have only
`propext`, `Classical.choice`, and `Quot.sound` in their closures. The
numerical zero-free region, low-height locations, and fixed-cutoff
Chebyshev-error theorem are still required for the final Dusart providers.

## Iterated Chebyshev smoothing

The next non-certificate step follows Dusart's HDR (2022), section 2.2,
Theorem 35. The Mathlib-only `IntervalIntegral.IteratedAverage` candidate
uses the existing `Monotone.intervalIntegrable`, interval integral
comparison, linearity, and the exact integral of the identity function.
Induction gives the support enclosure and exact mean shift at every
natural averaging order. `DusartPsiSmoothing` then directly applies
Mathlib's `Chebyshev.psi_mono`, retaining discontinuities and both sides
of the pointwise error estimate.

The inspected sibling `CharacterChebyshevDecay` applies BV's primitive
nonprincipal-character formula with existential constants; it does not
provide these fixed-constant zeta averages. Robin's inspected
`robinPrimePowerSum_eq_weighted_explicit_series` explicitly assumes RH.
Neither is treated as an unconditional numerical Dusart theorem. The
averaged explicit formula and its quantitative zero contributions remain
open; the new smoothing layer supplies only the pointwise recovery step.
Both modules compile, the eight regression examples pass, and all eight
audited exports have only the three standard logical axioms.

## Concrete box weight and actual averaged explicit formula

No replacement contour or zero-enumeration proof is necessary.
`DusartBoxExplicitFormula` applies the existing
`smoothedVonMangoldt_entire_explicitFormula` to the actual additive box
cutoff, discharging every hypothesis. The generic regularity candidate uses
Mathlib's `continuous_primitive`, `integral_interval_sub_left`, and FTC;
the exact derivative is the difference of the two endpoint values divided
by the interval width. Successive averaging therefore gives the required
two continuous derivatives without an assumed smooth cutoff.

The support candidate uses interval-integral congruence and continuity on
the closure to include the exact cutoff boundary. Endpoint derivatives
vanish by Mathlib's `IsLocalMax.deriv_eq_zero` and `IsLocalMin.deriv_eq_zero`.
A compactness bound on the second derivative is used only for convergence,
not as an unspecified constant in a claimed numerical estimate.

The arithmetic identification directly reuses `Chebyshev.psi_eq_sum_Icc`,
the natural floor/ceiling order equivalences, finite-sum integration, and
`tsum_eq_sum`. The resulting `DusartBoxAverageFormula` is an unconditional
identity for the actual averaged psi error, not a conditional replacement
formula. The xi index, multiplicities, and paired summability are unchanged.
Numerical bounds on its transforms and zero sums remain separate obligations.
All seven modules compile, 23 new and eight preserved regression examples
pass, and all 27 audited theorem closures use only the three standard
logical axioms. CI builds the candidate leaves and their consumers serially.
