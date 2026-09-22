# Lean completion handoff

This file records the current implementation boundary for Luna or any later
agent.  The objective is the exact all-`k` theorem in `Challenge.lean` and
`Solution.lean`.  Do not weaken the statement, import an unproved replacement,
or close an obligation with `sorry`, `admit`, an axiom, or `native_decide`.

## Current override: analytic replacement (2026-09-22)

The subsequent prime-prefix refactor also removes `RecordPrimeWitnesses`
from the required import graph and CI. `RecordPrefixBounds` derives its
38,000-prime count from `HasDusartPrimeCountingBounds`, now passed through
the finite-range lemmas. The final finite export is
`completeClassification_through38000_of_primeCounting`. This is not a new
assumption at the all-`k` boundary. The 380 generated parts are preserved but
not required. Historical prime-witness obligations below are superseded.

The full record-gap certificate is no longer required by `Solution`. The
instructions below about extending the full gap through `8600001` are
historical, not active obligations. Do not restore that dependency or its
181-job replay matrix. The existing smaller gap and twin certificates remain.

`PrimeReciprocalAbel.lean` and `PrimeCountingReciprocalShell.lean` prove the
finite reciprocal-prime shell directly from natural prime-counting bounds,
including the floor correction. `TailShellNumerics.lean` supplies the uniform
descent margin. `UniformTailClosedMertens.lean` now covers every `k >= 38001`,
using the existing ordinary Mertens estimate only for ascent. Its assumptions
are still prime counting, theta, and the uniform prime pair; it introduces no
sharp reciprocal-prime assumption. The tail and certificate-independent
`completeClassification_of_finite_prefix_and_primeCounting` both elaborate,
with axiom audits listing only `propext`, `Classical.choice`, and `Quot.sound`.

`CompleteClassificationCore.lean` applies this reduction to the existing
prefix through `38000`. Compatibility declarations named `full_record`
delegate to it without importing `FullRecordRange`. Challenge and Solution
are unchanged. CI checks the reduction in `analytic-tail`, then checks the
actual finite/provider assembly in the complete build. The three Dusart
providers below still require independent verification; the replacement
does not establish those inputs or certify the whole public theorem.

`scripts/check_tail_replacement.py` rejects full-gap imports transitively from
`Solution`; it runs in the fast pre-commit checks and CI. See
`RECORD_GAP_CERTIFICATES.md` for the proof boundary and verification command.
Legacy generated sources and caches are preserved, not scheduled for replay.

## Priority order

### Anchored Dusart comparison (newest, 2026-09-22)

`DusartJBounds` proves the actual Section 6.2 comparison from the 2010
Dusart paper: `J(x; -η) ≤ π(x) ≤ J(x; η)`, using the theta estimate only
on `[x₀, x]`. The anchor is exactly `π(x₀) - θ(x₀) / log(x₀)`.
`dusartJ_self` reduces the anchor check to prime counting and logarithms,
with no integral. `DusartJComparison` proves both printed derivatives and
the upper/lower differential comparisons. The generic logarithmic-power
derivative is now in the Mathlib candidate layer and also used by the
older Abel implementation.

`wangCrapis_primeCounting_of_paper_theta_estimates` wires this argument to
the unchanged natural prime-counting interface. Its remaining inputs are:

- a bounded prime-counting prefix through a chosen `x₀`, with `log x₀ ≥ 25`;
- the upper/lower theta errors `.05*x/log²x` and `x/log³x` above `x₀`;
- the two exact `J`/`M` comparisons at `x₀`.

These inputs are NOT proved by this adapter. The paper uses `x₀ = 10^11`;
the current checked prime-counting prefix is only 1000. The three global
declarations `wangCrapis_primeCounting`, `wangCrapis_thetaBounds`, and
`wangCrapis_shortInterval` remain missing. Next work must prove the paper's
theta estimates and anchor data, not treat the adapter as a closed provider.

The prime-counting assembly no longer accepts a log-fourth error coefficient
at most 1 starting at 2. A Lean regression disproves that input at `x = 4`.
Other legacy conditional interfaces in `MediumPNT`, `CompleteClassification*`,
and `WangCrapisClosed` still mention that impossible input; do not use them
as completion routes. The uniform `∀ Y` inputs in the eventual-cutoff
adapters are global obligations, not single finite computations.

The new analytic modules have no certificate imports; CI explicitly builds
the comparison and its candidate derivative before their consumers.
The candidate, both `J` modules, `DusartPrimeCountingAssembly`, and
`DusartPrimeCountingClosed` compile. `test/lean/DusartAnalytic.lean` passes,
including the `x = 4` counterexample and the published comparison constants.
All seven audited new exports use only `propext`, `Classical.choice`, and
`Quot.sound`. Fast source checks, Ruff, mypy, actionlint, and 70 Python tests
pass. Diagnostic logs are `.research/dusart-j-{build,final-build,regressions,axioms,fast}.log`.

### Closed prime-counting prefix through 1000 (newest, 2026-09-22)

`wangCrapis_primeCountingPrefix : HasDusartRealPrimeCountingBoundsBelow 1000`
is now genuinely proved and compiled. The earlier missing 599--1000 cover
described below is discharged, not an active gap.

`PrimeCountingCertificates` supplies compact rational rows with a reusable
kernel-checked assembler. `DusartPrimeCountingPrefix` stores one exact list of
168 primes through 1000 and 33 endpoint rows; its whole module compiles in
6.2 seconds. It covers every real point, including prime jumps and shared
endpoints. `scripts/generate_dusart_pi_prefix.py` deterministically reconstructs
the data using exact integers and fractions and records a semantic hash.

The representative row (including the shared prime-list proof) took 4.7
seconds and about 3.1 GiB peak RSS. Its earlier 4.2 GiB import footprint was
reduced by extracting the generic interval helpers into `IntervalCover` and
removing the unnecessary `EndpointBounds -> Core -> MediumPNT` dependency
from `PrimeCountingRows`. The row generator does not perform one new primality
computation per endpoint. Preserve that property.

`SmallPrimeCountingIntervals` now reuses the shared prime list for all 50
counts. The real errors were a smooth upper argument 120 < 163, the false
claim `primeCounting 271 = 57`, an underspecified logarithm lemma, and an
unclosed section. Corrected rows end at 270 and restart at 271 (whose count is
58). A checked natural-interval chain replaces 589 expanded coverage branches.
The corrected module compiles in 7.9 seconds; its former failing run took
71 seconds. No generated family or build cache was deleted.

The generated source is 92 lines. All focused Lean checks and the axiom audit
for `wangCrapis_primeCountingPrefix` pass (only the three standard logical
axioms). The fast gate, Ruff, mypy, 69 Python tests, deterministic regeneration,
actionlint, and whitespace checks pass. CI now checks the actual closed prefix
in the analytic job.

The full source theorem `wangCrapis_primeCounting` is still missing: this
prefix does not supply the fixed-constant analytic tail or the intervening
finite range. The theta and short-interval global providers also remain open.
Continue with those non-certificate obligations, including independently
checking the short-interval assembly, before large certificate families.

### Checked independent Dusart analytic chain (latest, 2026-09-22)

The persistent all-k goal is active again. Continue actual proof work; the
three global providers are still not proved and must not be assumed.

`DusartPrimePower` now owns the prime-power decomposition, integer-power
ratio comparison, large-index bound, and large-range Lemma 3.3 argument.
The intermediate power proof previously used these declarations before their
definition in a file that imported it. The dependency direction is corrected,
the ratio proof is repaired, and the new module compiles in about 8 seconds.
`DusartIntermediateLemma` also had a misspelled closing namespace, now fixed.
Its finite coefficient table has not been replayed as part of this repair.

`DusartRootBounds`, `DusartLemma33Assembly`, and `DusartThetaFromPsiBounds`
separate the analytic arguments from fixed endpoint computations. Both
`DusartThetaClosedPart01Tail` and `DusartThetaClosedPart02` now compile without
the generated endpoint chain. Repairs include cutoff transport, missing
arguments, strict-versus-nonstrict comparisons, and the actual tuple shape of
the medium-PNT result. A new proved strict numerical margin derives
`theta y > .9999*y` from the non-strict log-fourth error at `y >= 4e18`;
Proposition 3.1 can therefore use the stated non-strict error interface.

`DusartPrimeCountingAssembly` compiles independently too. Its finite facade
still needs a genuine covering prefix for 599--1000; do not restore the false
singleton cover. `PrimePrefixCounts` now proves that one checked largest
prime list supplies every smaller count by filtering. `PrimeCountingLogBounds`
proves rational log enclosures from comparisons of integer powers with
2--3--5-smooth integers. Both are compiled reusable primitives for that prefix.
Next implement and check the compact row assembler, then its covering data.
An exact-rational Python feasibility check found 33 overlapping-endpoint rows
covering 599--1000 using eighth powers and 2--3--5-smooth log enclosures.
The first endpoints are 599, 603, 610, 617, 630, 637, 644, 657, 671. These
are candidate data, not a Lean theorem. Prove one largest prime list and
filter it for all endpoint counts; do not repeat primality computation.

`DusartShortIntervalClosed` no longer has a forward reference to its tail
adapter and uses the existing below/above assembler name. The complete short
interval facade still awaits its finite dependency build; this change does
not certify the global short-interval provider. `DusartProofPart05/06` retain
compatibility exports and fixed finite consequences; they are not analytic
prebuild roots.

CI builds the independent theta and prime-counting chains in the analytic
job. `test/lean/DusartAnalytic.lean` exercises strict margins, prime-power
decomposition, shared prime counts, and powered log bounds. Python regression
checks prohibit dependencies back into `DusartProof` or the finite facade.
The paper's fixed-constant unbounded psi/theta estimates remain a separate,
genuine proof obligation; asymptotic existence cannot choose a verified
numerical cutoff by itself.
The focused Lean regression and axiom checks pass; the audited new theorems
use only `propext`, `Classical.choice`, and `Quot.sound`. The complete fast
gate, Ruff, mypy, 63 Python tests, actionlint, and whitespace checks pass.

### Checked theta-row repair (2026-09-22, later override)

The finite facade is now a small importer. Certificate-independent modules
`ThetaRows`, `ThetaEndpointRows`, `Table66Data`, `Table66Rows`,
`Table66Assembly`, `Table66EndpointFacts`, `PrimeCountingNumerics`, and
`PrimeCountingRows` were elaborated directly. CI builds the endpoint-facts,
small-theta, and prime-row targets in the analytic job before full replay.

`DusartThetaRelativeRow` now records the published `upper_coeff <= 1` and
the actual pointwise logarithmic lower error. Its assembler proves the
symmetric bound using `theta x <= x`. `Table66FormulaBounds.toRelativeRow`
uses the first logarithmic lower column at `x`; it does not replace that
logarithm with `log right`. Both previously invalid arguments described
below have been replaced and checked. The related chunk constructors now
require the table's actual `b0 <= 1` condition, not just a constant error.

The table's real coverage uses `dusartThetaTable66CellsChain_covers` rather
than the incorrect implication `left <= ceil x` implies `left <= x`.
Its 34 endpoints and all coefficient side conditions compile independently
of prime enumeration.

`DusartThetaClosedPart01` is rewritten and compiled. Exact small prime sums
prove the strict theta prefix through 29; monotonicity and rational log
enclosures prove the symmetric prefix through seven. All former exported
prefix declarations are retained. The invalid claim that singleton rows at
two and three cover their real interval is removed. Tests include `x=5/2`
and a nonintegral point immediately before a published table boundary.

The singleton prime-counting seed at 1000 is checked using the existing
`computablePrimesBelow_succ_length` theorem. Its old direct primality-decider
reduction reached roughly 9 GB and was terminated; the revised endpoint
module compiles in 5 seconds. Its coverage theorem now correctly covers only
the singleton, not the interval 599--1000. **Consequently the consumer
`wangCrapis_primeCountingPrefix` still needs actual covering rows for that
interval; its old use of the singleton theorem must be replaced.**

The three global Dusart declarations remain open. None of the above finite
results supplies the paper's fixed-constant unbounded psi/theta error.
The tail modules' reserved `prefix` identifiers were renamed and their
imports updated, but their complete elaboration still awaits the existing
Dusart proof/certificate dependency chain.

### Dusart endpoint correction (2026-09-22)

`DusartThetaTable66EndpointFacts` formerly imposed incompatible conditions
on the first published interval `[10^8, 2*10^8]`: its upper-zero field gives
`theta(10^8) <= 99998000`, while its lower-one endpoint requires
`200000000 - 550000/log(200000000) <= theta(10^8)`. Since the logarithm is
greater than one, these cannot both hold. This is now proved in Lean as
`dusartTable66_first_row_whole_endpoint_impossible`; do not try to generate
certificates for those old obligations.

The corrected package contains covering subinterval cells. Each cell stores
one pair of rational theta enclosures, reuses them for all six column
inequalities, and must prove its validity. A recursive boolean check and
`dusartThetaTable66CellsChain_covers` establish closed-interval coverage.
`Table66Bounds.lean` and `Table66Subintervals.lean` compile independently of
generated finite rows. The latter includes the incompatibility proof, and
`test/lean/Table66Subintervals.lean` checks coverage, gaps, ordering, and
endpoints. CI runs them before the complete certificate build.

The endpoint-facts consumer now takes an independently proved finite prefix
and coverage starting at that prefix's cutoff. It no longer asks the published
table, which starts at `10^8`, to cover from `2`. Two theta-tail adapters had
the same invalid prefix-to-table conversion; they now use the existing
prefix/table coefficient assembler. Its coverage arguments were also fixed.

Elaboration errors in the extracted formula helpers were repaired: a malformed
structure literal, a conjunction projection and `2 <= log` versus
`1 <= log` arguments, plus a missing cast normalization. The theta source
split also lost `wangCrapis_explicit_log_derivative_input`'s declaration
header and added unmatched `end` commands; these are restored. Helper
declarations now precede their consumers, including the public input-package
constructor. The complete provider modules still need elaboration once
their generated imports are available; the focused checks do not certify
those whole modules.

The facade's duplicated relative-row cover/assembler declarations were removed.
Indexed relative coverage now uses the generic upper/lower assembler directly,
not the nonexistent `hasDusartSymmetricThetaBoundsBelow_of_indexed_rows`.
Endpoint, strict-upper, and prime-counting helpers precede their consumers;
row-valued declarations use `def`, since their result is a data structure.

Further mathematical repair is needed inside the legacy relative-row adapters:
`dusartThetaRelativeRow_provides` attempts to deduce the upper half of the
logarithmic absolute error from a constant relative upper error with no bound
on `log x`. The published `b0 <= 1` conditions can instead give `theta x <= x`.
Also, `DusartThetaTable66Row.toRelativeRow` tries to strengthen a lower bound
by replacing `log x` with `log right`, which reverses the needed comparison.
Use the published constant-column bounds (already inputs) or prove the required
endpoint ratio margins; do not regard these existing tactic bodies as proofs.
Neither flaw is present in the independently checked `Table66Bounds` and
`Table66Subintervals` modules.

This repair does NOT supply the three missing global declarations
`wangCrapis_primeCounting`, `wangCrapis_thetaBounds`, and
`wangCrapis_shortInterval`. Actual theta enclosures and the fixed numerical
analytic bounds remain mathematical obligations. The existing
`explicitMediumPNT` concludes an existential constant and an `atTop` big-O
estimate; it does not by itself certify a particular cutoff or the finite
range up to that cutoff. Historical notes claiming only finite replay remains
must not be read as a proof of the fixed Dusart estimates.

For the 2016 explicit-psi route, use Dusart's corrected numerical formula,
not the two typographical errors in the published Theorem 3.5:
https://www.unilim.fr/pages_perso/pierre.dusart/Recherche/correctif_RJ.pdf
The correction is numerical source material, not a Lean proof of the
underlying zero/error bounds.

1. Finish and elaborate every non-certificate module.
2. Make the concrete analytic providers required by the all-`k` assembly.
3. Only then regenerate and replay expensive finite certificates.
4. Replace the two public placeholders after the internal universal theorem is
   closed and audit it with `#print axioms`.

Certificate jobs may run remotely while source work continues.  Local replay
success is useful only for finding errors; GitHub CI is the authoritative
large-memory replay environment.

## Non-certificate work still open

### Finite interval source split

This split is complete.  `FinitePrimeIntervalRows.lean` is the public facade;
the reusable definitions and conversions are in `FinitePrimeIntervalRows/Core.lean`
and `EndpointBounds.lean`, while the finite data is in `Low.lean` and
`High.lean`.  Low is generated by
`scripts/generate_finite_prime_interval_rows.py` into independent `LowPartNN`
chunks, each importing only `LowBase`; `Low.lean` imports all chunks and owns
the small aggregate list and chain declarations.  The generator test checks
that no Low chunk imports its predecessor and that stale chunks are removed.

Do not reopen this split or create one source file per witness.  Remaining
finite endpoint data must use the same compact row/assembler boundary and be
added only when it closes an analytic provider obligation.

The Proposition 5.4(c) logarithmic finite prefix is now represented by
`MediumLogRowsBase.lean`, seven generated `MediumLogBandNN.lean` data bands,
and `MediumLogRows.lean`.  It stores 22,115 adjacent-prime rows, including
the endpoint seed at `89693`, and exports the finite prefix through `360653`.
The scaled natural-number product constructor and ordered-chain assembler
are shared; do not replace this with one declaration or file per witness.

### Close the analytic provider by one canonical route

`Proof/CompleteClassification.lean` currently exposes many alternative
conditional packages.  Luna must not choose among them ad hoc or regard any of
those wrappers as closure.  The canonical final route is the three-field
`WangCrapisPaperInputs` boundary, because it states exactly the global analytic
facts used by the paper and does not force an infeasible endpoint enumeration
through `4e18` merely to construct `WangCrapisAnalyticInputs`.

Create `Proof/Analytic/WangCrapisClosed.lean` and close these declarations,
with these names and types:

- `wangCrapis_primeCounting : HasDusartPrimeCountingBounds`;
- `wangCrapis_thetaBounds : HasDusartThetaBounds`;
- `wangCrapis_shortInterval : HasDusartShortIntervalPrime`;
- `wangCrapisPaperInputs : WangCrapisPaperInputs`;
- `completeClassification_closed : CompleteClassification`, proved by
  `completeClassification_of_wangCrapis_paper_inputs wangCrapisPaperInputs`.

The first three declarations are the actual missing mathematics.  Prove the
explicit Dusart estimates from the sorry-free zero-free-region, Chebyshev,
Abel-summation, logarithm-envelope, and finite low-endpoint lemmas in this
repository.  Do not import a prepackaged Dusart theorem, repackage one as an
assumption, or substitute the existential-cutoff theorem from `MediumPNT` for
an explicit cutoff.  If a finite low range remains after the unbounded proof,
represent it as compact indexed rows with reusable assemblers.  Do not attempt
to enumerate prime-counting or theta endpoint rows all the way to `4e18`.

The intended source decomposition is:

- `Helpers/Analytic/DusartThetaClosed.lean` exports
  `wangCrapis_thetaBounds` after proving the explicit theta error and its
  finite low endpoint facts;
- `Helpers/Analytic/DusartPrimeCountingClosed.lean` exports
  `wangCrapis_primeCounting` by the proved Abel conversion and its finite
  low endpoint facts;
- `Helpers/Analytic/DusartShortIntervalClosed.lean` exports
  `wangCrapis_shortInterval`, using the compiled prefix through `89693` and
  the explicit theta estimate above that point;
- `Proof/Analytic/WangCrapisClosed.lean` only assembles those three exports.

### Paper-aligned Dusart dependency split

The global scope must follow the statements in Dusart's paper, not merely an
eventual asymptotic consequence:

- Proposition 3.2 is for every positive `x`.  Its proof separates the direct
  finite computation below `121` from the prime-power argument above `121`.
  The latter is now exposed as
  `dusart_proposition_3_2_of_uniform_strict_root_bound` and the global split as
  `dusart_proposition_3_2_of_uniform_strict_root_bound_all` in
  `DusartProof.lean`.
- Lemma 3.3 uses the published uniform theta estimate `theta x < 1.000081*x`
  and a finite check for the range where the displayed power-sum estimate is
  not yet effective.  An eventual Medium-PNT bound is not a replacement for
  this explicit constant.
- Proposition 5.1 uses the finite Table 6.6 check through `8*10^11`, the
  explicit psi error on `[8*10^11, exp 28]`, and the large-range theta error.
  The middle-range conversion is formalized in `DusartProof.lean`; the finite
  table and the explicit large-range input remain separate provider
  obligations.

Schoenfeld's page-360 improvement also fixes the natural finite theta split:
first prove the strict finite estimate `theta x < x` for `0 < x <= 8*10^11`,
then combine it with the large-range estimate to obtain the published
`theta x < 1.000081*x` bound.  The finite provider should therefore expose
the stronger `theta x < x` prefix and let the analytic tail supply the
`1.000081` constant, rather than certifying that relaxed constant separately
at every low endpoint.

The paper-reading check fixes an important boundary here.  In Lemma 3.3,
Dusart writes that the displayed power-sum estimate is effective only above
`(10^11)^3`; the assertion that the maximum of the remaining bounded
calculation occurs at `x = 2401` is the conclusion of that direct computation,
not a monotonicity lemma that discharges every `2401 < x < (10^11)^3`.
Consequently, the current exact `2401` row is a seed/checkpoint only.  The
global provider still needs either the complete bounded computation (encoded
as compact rows and assembled once) or a separately proved interval argument
covering the entire intermediate range.  Likewise, Proposition 5.1 explicitly
uses Table 6.6 through `8*10^11`; a small theta prefix cannot be promoted to
that published bound without proving the intervening table argument.

The finite-row facade also exposes `DusartThetaEndpointRow.toStrictUpperRow`
and `hasStrictThetaUpperBelow_of_endpoint_rows`.  These adapters consume an
explicit endpoint inequality `theta_upper < left`; they do not derive that
inequality from the relaxed Dusart error fields.  Use them for the Schoenfeld
strict Table 6.4 prefix once its bounded endpoint computation is available.

Table 6.6 needs a separate warning.  Its displayed `a0,b0` bounds are part of
three interval inequalities, with the accompanying `a1,b1` and `a2,b2`
corrections in `1 / log x` and `1 / log^2 x`.  Monotonicity of `theta` plus a
single endpoint value cannot certify a constant-coefficient row on a
nontrivial interval: the lower and upper margins move with `x`.  The verified
table-row boundary must therefore retain a direct interval proof (or formalize
the full three-coefficient formula); do not replace it with endpoint-only
inequalities.

The Proposition 3.1 finite-row interface uses half-open unit intervals
`[n,n+1)`, not closed singleton intervals.  Its integer reduction therefore
checks the shifted margin at `sqrt (n+1)` before transporting the constant
`psi - theta` value across the interval.  Any future bounded-data generator
must preserve this shifted endpoint condition.

These are source obligations before certificate replay.  A certificate may
 discharge only the finite computation it actually represents; it must not be
 used to hide a missing analytic theorem or to weaken an all-`x` statement to
 an eventual one.

The dependency audit also found a proved (non-placeholder) `ZetaZeroFree`
lemma in `PrimeNumberTheoremAnd/ZetaBounds.lean`.  It supplies an existential
`A` and a region of the form `1 - A / log(|t|)^9`; it does not supply the
explicit fixed numerical parameter or the sharper classical region needed by
Dusart's constants.  The `MediumPNT` consequence therefore remains an
eventual existential decay result.  Do not mistake that theorem for the
completed explicit Dusart analytic tail: the missing work is the numerical
specialization and its Chebyshev-error conversion.

The local `PrimeNumberTheoremAnd/IEANTN/Dusart.lean` is not a usable fallback:
its matching `proposition_4_4` declaration for the (1.777745) Lemma 3.3
bound has a placeholder proof.  It must remain excluded from the dependency
chain.

Preserve the existing generic declarations in `DecayToLogFourth.lean`,
`ExplicitPrimeCounting.lean`, `ExplicitThetaBounds.lean`,
`ShortIntervalPrime.lean`, and `MediumPNT.lean`; repair their elaboration
errors before writing the final assembly.  The fixed-cutoff
`Dusart599IndexedFiniteCertificate` route remains a useful generic interface,
but it is not the selected final route and is not a license to generate a
table through `4e18`.

### Raise the finite record theorem to the published cutoff

Implementation note: the current descent inequality's certified numerical
margin supports `k ≤ 7,300,000`; widening `fullRecord_descentNumeric` itself
to `8,600,001` is not valid with its present logarithm and Mertens-error
constants. The published `8,600,001` theorem must therefore continue to use
the already proved closed-Mertens tail for `k ≥ 7,300,001`, as
`fullRecordRange_not_isUnimodal_closed_through8600001` does. Do not replace
that overlap with a numeral-only widening of the descent proof. Any future
attempt to make the descent inequality itself reach `8,600,001` must first
add and prove genuinely stronger numerical bounds.

This is non-certificate proof work and must be completed before any expensive
replay.  The side-condition module already reaches `k = 8,600,001`, but the
numeric descent remains hard-coded to `7,300,000`, which is the verified
descent cutoff. The final published split already reaches `8,600,001` by
using the closed tail from `7,300,001`; merely extending the record-gap
owners does not change the descent inequality.

The required source-level checks are therefore:

1. Keep `fullRecord_prefix_log_log_lt` valid through `8,600,001`, as it is.
2. Keep `fullRecord_descentNumeric` at its certified cutoff
   `k ≤ 7,300,000`; its proof uses `k - 1 ≤ 7,299,999`.
3. Keep `fullRecordRange_not_isUnimodal` and
   `fullRecordRange_not_isUnimodal_closed` at `7,300,000`, and use
   `fullRecordRange_not_isUnimodal_closed_through8600001` for the published
   range.
4. Keep `completeClassification_of_finite_record_range` at cutoff
   `8,600,001`, with the uniform tail beginning at `8,600,002`.
5. Check `completeClassification_of_full_record_inputs` in
   `Proof/CompleteClassification.lean`, with cutoff `8600001`; every adapter
   above it must elaborate without reintroducing `7430000`.

Keep the independently proved tail's earlier validity (`k ≥ 7,300,001`) if it
is useful, but the public finite theorem and final split must still state the
paper's full `8,600,001` cutoff.  A final source scan for `7430000` and
`7429999` outside historical comments must return no live theorem dependency.

The final internal theorem is `completeClassification_closed`; only after that
declaration is source-complete should both public declarations named
`PrimeFactorUnimodality.completeClassification` in `Challenge.lean` and
`Solution.lean` be filled with it.

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

### Record-twin replay compression

The four `RecordTwin*SeedChunks` and `RecordTwin*SeedTail` directories contain
about 1,900 files and another 287 MiB.  Their large state literals are repeated
as one chunk's output and the next chunk's input, and the tail representation
duplicates much of the chunk machinery.  Treat this as the same architectural
problem rather than accepting one file per step.

After the analytic modules are complete, prototype a row containing 8--32
power steps:

1. Store the initial state once and the ordered chunk widths/values once.
2. Compute intermediate states through a reusable recursive `PowerTrace` row
   assembler instead of emitting independent `Before` and `State` literals for
   every step.
3. Keep enough checkpoint states to bound elaboration and permit CI sharding;
   checkpoints are an engineering parameter, not theorem declarations.
4. Export the exact final lower/upper trace theorem names consumed by
   `RecordTwinClosed.lean`.
5. Compare source bytes, peak memory, and replay time for one prototype row.
   Prefer a modest source increase if it materially lowers kernel memory.
6. Replace and remove the old chunk/tail trees only after both complete trace
   endpoints replay in CI.  Preserve the semantic hashes in generated module
   comments and generator tests.

Do not combine the lower and upper primality computations into one giant Lean
declaration.  They should remain separately cacheable CI targets even after
their internal steps are row-compressed.

## Exact finite-certificate consumer matrix

The certificate skeleton is complete only when each producer below exists in
source, exports the stated stable name, and its non-generated consumer has
already elaborated against a representative row.  A generated file merely
existing is not enough.

### Small record range (`49 ≤ k ≤ 38000`)

- `Generated/RecordPrimeWitnesses.lean` must export
  `recordPrimeWitnesses_card` and `recordPrimeWitnesses_subset`;
  `RecordPrefixBounds.lean` must then elaborate
  `record_primeCounting_500001_ge`, `record_prefix_primeAt_le_500000`, and
  `record_prefix_log_log_lt`.
- `Generated/RecordReciprocalBlocks.lean` must export
  `roundedReciprocalSieveSumBelow_500001_eq`;
  `RecordReciprocalCertificate.lean` must then elaborate
  `reciprocalPrimeSumBelow_500001_lt`.
- The compressed lower and upper power traces must preserve
  `recordLower_main_kernel`, `recordLower_proper_2_kernel`,
  `recordLower_proper_3_kernel`, `recordLower_proper_17_kernel`,
  `recordLower_proper_4950817_kernel`, and the corresponding five
  `recordUpper_*_kernel` declarations, plus `recordUpperWitnessBase`.
  `RecordTwinClosed.lean` must then elaborate `recordTwinCertificate`,
  `recordTwin_isTwinPrime`, and `recordTwin_consecutive`.
- `ClassificationThrough38000Closed.lean` must elaborate
  `completeClassification_through38000_closed` from those closed consumers.

The prime-witness and reciprocal sources already exist; unless CI finds an
elaboration error, they are build/fix work rather than open mathematical
design.  Do not redesign them while a non-certificate obligation remains.

### Full published record gap (`38001 ≤ k ≤ 8600001`)

- The compact subtraction owner rows must export
  `fullRecordGapSubBlock (d : Nat) (lower : 1 ≤ d) (upper : d ≤ 455703) :
  ¬(recordGapCenter - d).Prime`.
- The compact addition owner rows must export
  `fullRecordGapAddBlock (d : Nat) (lower : 1 ≤ d) (upper : d ≤ 657401) :
  ¬(recordGapCenter + d).Prime`.
- Their only non-generated assembly API is
  `fullRecordGapSubBlock_of_rows` and `fullRecordGapAddBlock_of_rows` from
  `RecordGapOwnerRows.lean`.
- The 10,918 Fermat-only offsets remain theorem-addressable, but their replay
  data is stored and checked in the existing 171 shared rows.  The compact
  owner table references those row results; it must not emit a file or a full
  modular-power trace per offset.
- `FullRecordRange.lean` consumes exactly the two block theorems and
  `recordTwin_consecutive`; after the numeric-cutoff work above it must export
  `fullRecordRange_not_isUnimodal_closed` through `8600001`.

Before full generation, compile one 512-offset mixed owner row and one 8--32
step power-trace row.  That representative-row benchmark is a source-design
gate, not an optional performance experiment.

## Remaining elaboration-risk audit

No claim that “only CI remains” is valid until Luna has run focused builds for
all non-generated modules below.  They contain new or currently unbuilt APIs
whose source shape alone does not prove elaboration:

1. the five-way `FinitePrimeIntervalRows` split and its facade;
2. `DecayToLogFourth`, `ExplicitThetaBounds`, `ExplicitPrimeCounting`,
   `ShortIntervalPrime`, and `MediumPNT`;
3. the three `Dusart*Closed` modules and `WangCrapisClosed`;
4. `RecordGapOwnerRows`, `FullRecordNumericBounds`,
   `CompleteClassificationReduction`, and `CompleteClassification`;
5. the reusable compressed `PowerTrace` assembler and one lower/upper sample;
6. all non-generated consumers named in the certificate matrix above.

When a focused build reports an elaboration error, fix source immediately and
continue down this list.  Do not wait for a full certificate replay to finish.

### Known source-policy failures from the current fast check

The September 19 fast check is not clean.  Luna must close these named issues
rather than discovering them at release time:

- `Challenge.lean` directly imports the project module
  `PrimeFactorUnimodality.Definitions.KthPrimeFactor`; restore the required
  challenge boundary while preserving the exact all-`k` statement.
- Put imports in ordinal order in `ExplicitPrimeCounting.lean`,
  `ExplicitThetaBounds.lean`, `FinitePrimeIntervalRows.lean`,
  `MediumPNT.lean`, `RelativePsiTheta.lean`, `CompleteClassification.lean`,
  `ElementaryTailShell.lean`, and `TailErrorBounds.lean`.
- The old `FullRecordGapFermat` rows and `FullRecordGapOwners` forest produce
  thousands of missing-module-documentation and import-order failures.  The
  compact replacement generators must emit compliant module documentation and
  sorted imports from their first prototype.  Do not mechanically repair the
  obsolete per-witness forest before replacing it.
- `Solution.lean` and `Challenge.lean` remain the only intentional `sorry`
  surfaces; both disappear when `completeClassification_closed` is installed.

The fast check also confirmed a clean documentation manifest, clean public
boundary, and current submission link.  Its current failure is therefore a
real open gate, not a tooling crash.

## Definition of “skeleton complete; only CI remains”

All of the following must be true simultaneously:

- every module and declaration named above exists in tracked source;
- every non-generated module builds locally, except that a final consumer may
  be blocked solely by a named generated import that is already committed;
- all compact generators have emitted their complete row data and deterministic
  manifests, not merely prototypes;
- generated facades export every stable producer name in the matrix, and the
  old per-witness forests are no longer imported by the active graph;
- `PrimeFactorUnimodality.lean` imports `Proof.Analytic.WangCrapisClosed`, and
  both public theorem bodies use `completeClassification_closed` with no
  placeholder;
- repository scans find no `sorry`, `admit`, project-local `axiom`, bodyless
  `constant`, `opaque`, or `native_decide` in the active proof graph;
- source scans find no live `7430000`/`7429999` cutoff and no accidental
  assumption-backed Dusart provider;
- deterministic generator tests and the fast policy check pass;
- CI is re-enabled with foundation jobs before separately cacheable heavy
  certificate jobs.

Only the kernel replay of the already committed generated rows, followed by
`#print axioms` and release checks, may remain after this gate.  If code still
needs to be designed, a theorem body still needs to be written, a generator
has not emitted its final data, or a consumer has never elaborated against a
representative row, then the project is not yet in the “waiting on CI” state.

## CI staging

The workflow is intentionally disabled at the GitHub level until source work
is ready.  When re-enabled, the `Lean foundations` job should elaborate the
analytic and reusable row infrastructure first.  The full build remains the
expensive certificate phase and must depend on that job.  Run large targets
one at a time if memory pressure appears; preserve `.lake` caches between
diagnostic runs.

The tracked files currently contain `633,923,177` bytes (about 604.6 MiB) of
logical data, while Git's packed object database is about 165 MiB.  Filesystem
tools report about 808 MiB allocated for the worktree excluding `.git` and
`.lake`; the thousands of small generated files add block-allocation overhead,
but most of the roughly 634 MB figure really is tracked generated certificate
source.  The public-boundary limit is now 1 GiB; that change does not remove or
rewrite any data.

## September 19 analytic progress

The following sorry-free assembly boundaries are now pushed:

- `wangCrapis_thetaBounds_of_rpowDecay` converts an underlying theta
  `HasThetaLogRpowDecay` estimate to the exact global theta provider once the
  finite endpoint verification is supplied.
- `wangCrapis_thetaBounds_of_mediumPNT` performs the same assembly from the
  source-level medium-PNT adapter and an explicit finite endpoint provider.
- `wangCrapis_shortInterval_of_mediumPNT` assembles the exact global
  short-interval provider from the source-level medium-PNT tail and a finite
  log-cubed row provider.
- `wangCrapis_thetaBounds_of_indexed_endpoint_rows_and_tail` assembles the
  global theta provider from compact indexed Table 6.4-style endpoint rows
  and an explicit log-fourth tail.
- `dusart_proposition_3_2_of_indexed_rows_and_theta_bounds` assembles the
  all-`x` Proposition 3.2 bound from compact indexed Lemma 3.3 rows and the
  separately proved theta provider.

The earlier tail assemblies are in commits `10dca102` and `9080f4ca`; the
indexed endpoint and Lemma 3.3/Proposition 3.2 assemblies are in commits
`2904169f` and `f40e48c5`.

The BKLNW shortcut was audited and rejected: `BKLNW.thm_1a` depends on
`BKLNW_app.theorem_2`, whose source declaration is `by sorry`. Therefore no
provider may import `thm_1a`, `thm_1a_crit`, or `thm_1a_table` as the final
Dusart proof until that underlying theorem and its transitive dependencies are
proved. The admissible next analytic target is the first missing source-level
decay/explicit-estimate theorem, not another wrapper around the BKLNW
placeholder.

## September 20 paper-aligned Dusart boundaries

The following additional source-level boundaries are now pushed through
`033b2f2b`:

- `dusart_proposition_3_1_of_finite_and_thetaErrorAbove` converts the exact
  `HasThetaLogFourthErrorAbove (648 / 1000) (4e18)` tail into Dusart's
  Proposition 3.1 after its bounded interval is proved.
- `dusart_proposition_5_1_tail_of_logFourthError` derives the Proposition 5.1
  large range beginning at `exp 28` from an explicit log-fourth error.
- `wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError` derives the
  middle-range `psi - theta` gap through Proposition 3.1, rather than taking
  that gap as an independent theorem.
- `wangCrapis_thetaBounds_of_paper_finite_prefix_and_logFourthTail` combines
  separate finite upper and lower theta obligations with the analytic tail;
  the finite lower estimate is no longer forced into a symmetric endpoint
  row.

The remaining non-certificate inputs are therefore the actual bounded
verification data (Dusart's Table 6.4 upper range, the bounded part of
Proposition 3.1, and the lower-theta prefix), plus the explicit zero-free
region/error proof that supplies the `648 / 1000` tail. These are not
discharged by the adapters above and must remain open until their underlying
arguments or compact reusable row assemblers are formalized.

The first unresolved numerical analytic chain is upstream of `ZetaZeroFree`:
`ZetaLowerBnd` constructs its region parameter from the existential constants
in `ZetaLowerBound3` and `Zeta_diff_Bnd`; those in turn use
`ZetaUpperBnd`, `ZetaNear1BndExact`, and `ZetaDerivUpperBnd`. The source
proofs establish positivity but do not expose rational lower bounds for the
region parameter. A direct fixed-Dusart tail proof must therefore strengthen
that chain at its first numerical bound, rather than choosing a fixed value
after `ZetaZeroFree` has already hidden the parameter existentially.

## September 20 dependency audit

The explicit finite-range shortcut through the upstream Büthe/BKLNW files is
not an admissible proof route. `PrimeNumberTheoremAnd/IEANTN/Buthe.lean`
declares `Buthe.theorem_2c` with a placeholder body, and
`BKLNW.buthe_eq_1_7` proves its `theta x < x` prefix by invoking that theorem.
The corresponding BKLNW table and FKS2 aggregate declarations also inherit
placeholder-backed numerical inputs. They must not be imported into the
canonical providers.

The reusable project-side interfaces that remain valid are:

- `hasStrictThetaUpperBelow_of_indexed_rows` and
  `hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows` for compact
  finite theta data;
- `wangCrapis_thetaBounds_of_indexed_endpoint_rows_and_tail` for the global
  theta assembly;
- `dusart_proposition_3_1_of_finite_and_thetaErrorAbove` and
  `dusart_lemma_3_3_of_indexed_rows_and_theta_bounds` for the exact all-range
  Dusart splits.

This audit is a dependency exclusion, not a closure of the outstanding
mathematics. The next source implementation must prove the finite numerical
facts or their reusable row assemblers directly, and must expose the fixed
analytic tail constants without passing through those upstream placeholders.

## September 20 explicit zeta progress

`Helpers/Analytic/ZetaExplicitBounds.lean` now records the paper's elementary
zeta-side constants directly: the real-axis near-one estimate, the explicit
upper and derivative bounds, the integrated zeta-difference estimate, an
explicit symmetric lower bound in the zero-free strip, and the resulting
uniform logarithmic-derivative bound.  The latter is assembled with the
large-real-part Dirichlet-series monotonicity estimate and the elementary
pole-distance estimate.

`Helpers/Analytic/ExplicitMediumPNT.lean` is generated from the explicit-formula
proof body and replaces the package's existential logarithmic-derivative input
with `zetaLogDeriv_explicit_bounded_and_holo`.  The project `MediumPNT.lean`
adapter now consumes `explicitMediumPNT`.  This closes the zeta-bound input
boundary.  The downstream adapter derives
`HasThetaLogFourthErrorAbove (648 / 1000)` at an existentially selected
cutoff; the finite provider must be instantiated at that same cutoff.  This
does not turn the existential tail theorem into a finished Dusart provider:
the finite endpoint rows and their cutoff-dependent assembly are still
required.

The source boundary after this adapter is now explicit: the remaining work is
the paper's finite Table 6.4, Proposition 3.1, and Lemma 3.3 computations,
together with the finite prime-counting and short-interval assemblers.  Do not
reopen the zeta/PNT source route while those rows are being constructed; keep
the computations behind indexed reusable row interfaces.

## September 21 medium-PNT axiom audit

The imported `PrimeNumberTheoremAnd.MediumPNT` declaration was checked with
Lean's axiom printer, and the local `explicitMediumPNT` wrapper was checked in
the same way.  Both surfaces contain only `propext`, `Classical.choice`, and
`Quot.sound`; the apparent `axiom` examples in the custom additive-combination
tactic are inside its documentation comment and are not declarations.  The
medium-PNT and logarithmic-decay route is therefore an admissible source
dependency.  The remaining provider work is finite numerical verification and
its reusable row assemblers, not a replacement proof of that PNT theorem.
