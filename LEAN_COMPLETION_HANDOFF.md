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

### Outer height-tail master (newest, 2026-09-22)

The rational outer-strip comparison, both reflected pair errors, and their
actual multiplicity-counted series assembly are now proved. The cutoff and
separation conditions remain visible; this does not prove a numerical
zero-free region or finish the Dusart providers.

- `Poisson.OuterStrip` allows `1/2<σ₀<=σ<=β<=1`, retaining the negative
  numerator `σ-β`. It bounds both rational pairs and proves their difference
  nonnegative for every `y²>=H²`, provided the explicit gap and endpoint
  inequalities hold. No `σ>1` lemma is used inside the strip.
- `KadiriOuterPairs` sets `a=σ₀-1/2`, proves the three positive-real-part
  bounds from `δ>=1/2`, and removes the nonnegative rational term. Reflection
  extends the error to both outer strips. The uniform coefficient is
  `E=η² M(z,θ)+(1+2κ)η³m/(σ₀-1/2)`, with `z<=(σ-1)/η`.
- `Series.Imaginary` transfers inverse-square norm summability to imaginary
  denominators on separated bounded strips. `XiHeightTail` applies the
  existing unconditional shifted xi summability theorem. Its actual tail is
  `Σ(t,H)=sum_{|γ|>=|t|+H} 1/(t-γ)²`, preserving multiplicities. For `t>=0`
  this is exactly Mossinghoff--Trudgian (4.1), not the larger set of all
  zeros with `|t-γ|>=H`. The norm comparison proves convergence only.
- `KadiriOuterTail` proves `-E/2*Σ(t,H) <= sum_outer D(s-ρ)` when every
  outer zero has `|γ|>=|t|+H`. The half factor is the proved exact pairing
  identity, not a dropped multiplicity. Nonnegative harmonic weights are
  handled by `kadiriWeight_weighted_outer_zero_sum_lower_bound`.
- `KadiriTailMaster.kadiriWeight_tail_master_nonneg` inserts that inequality
  into the actual distinguished-zero master, retaining the pole/gamma terms
  and the already-proved distinguished-pair polynomial error explicitly.

The two candidates, four project leaves, and complex facade compile.
All 17 theorem exports audited by `.research/DusartOuterTailAxioms.lean`
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
CI builds this chain serially in `lean-foundations`, then runs the regression
`test/lean/KadiriOuterTail.lean`. It covers signed heights, cutoff equality,
unrestricted negative first numerators, norm-to-height summability, and the
exact paper tail domain. Its toy rational parameters are not numerical
certificates for `R=5.573412`.

NEXT: prove the absolute-height separation from the underlying zero-free
and low-zero inputs, then the actual quantitative `Σ(t,H)` bound. For
positive height, use conjugation with multiplicities to rewrite `Σ` as the
positive-height sum of `1/(γ-t)²+1/(γ+t)²`, then prove the required Lehman
estimate from its counting/integration argument. Preserve the cutoff's
closed endpoint; a strict-tail theorem needs a checked endpoint correction.
At height zero, the paper uses the unconditional inverse-square total bound
minus a verified low-zero contribution; an RH-dependent xi mass theorem
does not discharge it. Pole/gamma bounds, the exact parameter and moment
checks, and the three final Dusart providers are also still open. Continue
non-certificate source work first. Earlier NEXT instructions to construct
the rational comparison or outer-series assembly are superseded.

### Weighted outer-pair remainder (2026-09-22)

The exact derivative-mass remainder and its four-moment majorant are now
proved, and the four error terms in Kadiri (49) are assembled pointwise.
No coarse supremum or right-half-plane-only theorem replaces the paper's
negative-line estimate.

- `FiniteLaplace.WeightedBounds` retains the exact Laplace transform of
  the source norm. `KadiriDerivativeMass` defines the actual integral
  `M(z,θ)=∫|hθ''(u)|exp(-zu)du`, proves nonnegativity and antitonicity,
  the positive-axis bound `M(x)<=m/x`, and exact second-derivative scaling.
- `KadiriWeightedRemainder` proves the pole-subtracted identity and
  `|Re F(s)-f(0)Re(1/s)| <= η² M(Re(s)/η,θ)/|s|²` at every nonzero `s`,
  with NO sign restriction on `Re(s)`. A lower bound `z<=Re(s)/η` gives
  the uniform `η² M(z,θ)/Im(s)²` bound; the positive-axis terms have the
  separate uniform cubic bound `η³m/(a Im(s)²)` for `0<a<=Re(s)`.
- `Exp.Cubic` uses Mathlib's exponential series to prove that a cubic
  majorant checked at one positive endpoint holds on the entire interval.
  `Integrals.ExpMoments` integrates it against any continuous nonnegative
  source. `KadiriDerivativeMoments` specializes this to the actual four
  moments and the paper's exact denominator `3.45`, then feeds it into
  the transform remainder. The exponential endpoint and numerical moment
  values are explicit remaining finite inputs, not certified by this step.
- `KadiriOuterPairRemainder.kadiriWeight_outer_pair_remainder_lower_bound`
  proves the actual smoothed pair is at least its rational four-kernel
  contribution times `f(0)`, minus
  `[η² M(z,θ)+(1+2κ)η³m/a]/y²`. The rational term remains explicit;
  its inside-strip large-height sign is NOT assumed proved.

For `z<=0`, all four coefficients of `M*` are nonnegative, including the
odd moments: `kadiriDerivativeMassMajorant_le_of_moment_bounds` proves
the upper-bound substitution directions for ALL four moments. Use that
theorem when assembling numerical bounds; do not infer a rounding direction
from the minus signs without accounting for the sign of `z`.

All three new candidates, four project leaves, and both affected facades
compile. All 23 exports in `.research/DusartWeightedRemainderAxioms.lean`
audit only the standard three axioms. The new regression covers complex
sources, negative rescaling, the imaginary axis, a discharged cubic
endpoint, moment-bound directions, and the assembled pair error.
Fast prebuild, Ruff, mypy, workflow lint, all 95 Python tests, and the
16 Ruby tests (83 assertions) pass. CI builds the new leaves serially in
`lean-foundations` and runs `test/lean/KadiriWeightedRemainder.lean`.

The rational comparison and outer-series assembly have since been proved
in the newer section above. Remaining work includes the zero-tail count/integral estimates,
pole and gamma bounds. The exact `R=5.573412` numerical inputs and all
three final Dusart providers remain open. Non-certificate source still
comes before numerical replay; do not redo the weighted-mass/moment work.

### Quantitative distinguished zero (newest, 2026-09-22)

`KadiriDistinguishedZero.kadiriWeight_distinguished_master_nonneg` now
retains the actual distinguished transform in the master, with the exact
linear/cubic pair error and the complete outer-strip remainder. Its scale
is `η=1-Re(ρ)`, its selected harmonic has frequency one, and its divisor
label is genuinely off the critical line. There is no assumed pair bound
at the consumer boundary; it is proved in the new chain:

- `KadiriRetainedZeros` retains one pair at any selected harmonic by
  applying Mathlib's finite-subsum bound to the nonnegative differences
  between the full and outer contributions.
- `KadiriRetainedMaster` combines that bound with the actual master.
- The Mathlib-only `FiniteLaplace.Monotonicity` proves the real integral
  identity and antitonicity for nonnegative compact sources on the ENTIRE
  real axis, including negative arguments.
- `KadiriRetainedBounds` proves Kadiri equation (34), section 4.1.1.
  Monotonicity bounds the three regular transform terms at `1`, `δ`, and
  `σ₀-η₀+δ`; the existing cubic error gives their explicit constants.
  `kadiriRetainedPairError` is exactly
  `[(κ(1/δ+1/c)-1)g₁]η + [(1+κ(1/δ³+1/c³))m]η³`,
  where `c=σ₀-η₀+δ`, `g₁=kadiriKernel θ 0`, and `m=-kadiriKernel₂ θ 0`.
  The main transform is not divided by `σ-β`; the case `σ=β` is covered.
- `KadiriDistinguishedZero` applies this to the actual xi zero and obtains
  both the weighted zero-sum lower bound and the quantitative master.

The new candidate, four project leaves, and `test/lean/KadiriRetainedZero.lean`
compile. Ten theorem exports audit to `propext`, `Classical.choice`, and
`Quot.sound` only (`.research/DusartRetainedZeroAxioms.lean`). The regression
checks negative-axis monotonicity, the exact error signs, `σ=β`, and the
frequency-one term in a degree-16 sum. CI builds the candidate before its
facade/consumers and the four leaves serially before the regression.
Fast prebuild checks, workflow lint, Ruff, mypy, all 94 Python tests, and
all 16 Ruby metadata tests (83 assertions) pass. No full-project build or
CI success is claimed for the still-missing Dusart providers.

The exact weighted transform remainder, scaling, and symbolic cubic moment
majorant proposed at this stage are now proved above. For the remaining
rational four-kernel term, `stechkinZeroPair_sub_nonneg` assumes
`σ>1` and cannot justify positivity here: this needs its inside-strip,
large-height comparison proved with explicit parameter bounds.

For the zero-tail sum, use Mossinghoff--Trudgian section 4 / (4.1): their
`c₃₀` uses Lehman's integral estimate for positive heights and checked
low-zero subtraction at height zero, not Kadiri's older counting estimate.
The required exact `R=5.573412`, degree-16 polynomial, and numerical inputs
are still unproved. All three final Dusart providers and the all-`k`
completion remain open. No certificate replay is needed for the next
analytic source work. Do not redo the distinguished-zero integration.

### Actual multiplicity-counted zero sums (newest, 2026-09-22)

The paired comparison is now integrated with the actual xi divisor.
See `DUSART_ZERO_REUSE.md` for the focused sibling audit at exact published
revisions. BV/PNT's local conjugation/order argument is reused as a
Mathlib-only candidate; the existing project xi function symmetries and
Mathlib infinite-sum API are reused rather than reproved. RH-dependent
shifted mass estimates and `Re(s)>1` positivity were not substituted for
the unconditional smoothed strip argument.

- `ZetaXiDivisorConjugation` builds `ρ -> 1-conj(ρ)` as an involutive
  equivalence preserving each `Fin` multiplicity label. Its fixed points
  are exactly the critical-line labels.
- `ZetaXiDivisorPairing` proves exact half-pair reindexing on the full
  divisor and reflection-stable subtypes, central-pair elimination, and
  retention of one distinguished nonfixed pair. The reusable
  `Summable.pair_le_tsum_of_involution` uses Mathlib's finite-subsum bound
  on the symmetrized series, not positivity of individual terms.
- `KadiriZeroSummability` supplies actual-weight summability at EVERY
  complex argument. `KadiriZeroSums` proves the central-strip contribution
  nonnegative, bounds the outer sum by the full sum, and retains an
  off-critical pair plus the entire outer contribution. All weight and
  pair hypotheses are discharged using the previously proved symbolic
  κ₂/κ₃ comparison.
- `KadiriOuterMaster` inserts central-strip elimination into the actual
  master inequality, keeping pole, outer-zero, and gamma terms explicit.
  This particular master discards all central pairs; its retained-pair
  refinement and distinguished-pair estimate are now supplied by the newer
  chain above. The remaining outer-zero/pole/gamma estimates are still open.

All new leaf modules and `test/lean/KadiriZeroSums.lean` compile. All 28
audited declarations use only the standard three axioms; probe/log are
`.research/DusartXiPairingAxioms.lean` and
`.research/dusart-xi-pairing-axioms.log`. CI builds candidates before their
consumers, serially in `lean-foundations`. Regression examples exercise
signed summands, infinite analytic order, fixed points, label preservation,
and actual retained-pair sums. The fast prebuild profile (including source,
architecture, exact Challenge/Solution, Ruff, and Ruby metadata checks),
workflow lint, mypy, and all 93 Python tests pass. Ruby reports 16 tests,
83 assertions, and no failures or skips. No full-project CI success or final
Dusart proof is claimed.

The distinguished-pair weighted integration and quantitative lower bound
proposed at this stage are now proved in the newer section above. The
remaining outer-zero and gamma estimates must use the exact
Mossinghoff--Trudgian parameters. The target remains `R=5.573412`.
Then prove the needed sharp PNT bounds and finite analytic inputs for
`wangCrapis_primeCounting`, `wangCrapis_thetaBounds`, and
`wangCrapis_shortInterval`. All three providers remain open. Do not redo
conjugation, multiplicity transport, summability, or central elimination.
For elaboration, explicitly supply `G := fun ρ => ...` and the complex
argument when applying generic sum lemmas: leaving them as `_` caused
unnecessary unfolding of `finiteLaplace` and heartbeat exhaustion.

### Smoothed paired-zero inequality (newest, 2026-09-22)

`KadiriPairedZeros.kadiriWeight_paired_zero_nonneg` proves the actual
paper-weight comparison
`D(σ-β+iy) + D(σ-1+β+iy) >= 0` for EVERY real `y`, including zero,
EVERY `1-σ <= β <= σ`, `1/2 < σ₀ <= σ <= 1`, and `0 < η <= η₀`.
Its parameter assumptions are `δ>0`, `κ>=0`, and the exact symbolic
`κ <= κ₂, κ <= κ₃` from the paper. `KadiriPairParameters` defines those
two quotients with `r₀=2*σ₀-1` and the actual `g₁` and sharp `m`.
There is no boundary-positivity premise, height cutoff, sampled numerical
check, or polynomial-coefficient premise at this theorem's boundary.

The proof chain is complete for this comparison:

- `Poisson.ThreeKernel` proves that two nonnegative endpoint coefficients
  force the full rational comparison at every height.
- `Poisson.ThreeKernelUniform` proves those coefficients uniformly for
  `r₀<=r<=1` and a bounded nonnegative error coefficient. It retains the
  exact denominators in the paper's κ₂/κ₃, not rounded replacements.
- `PhragmenLindelof.RealPart` applies the analytic strip principle to
  `exp(-F)`. `FiniteLaplace.RealSource` supplies conjugation and the compact
  source's uniform half-plane bound; `FiniteLaplace.PairedStrip` transfers
  a reflected comparison from the imaginary edge to the whole strip.
- `KadiriPairedStrip` combines the proved H2 and cubic error on that edge.
  `KadiriPairParameters` discharges its coefficients using κ₂/κ₃ and exact
  scaling. Conjugation gives the final same-height comparison.

The tests cover arbitrary parameters/heights, both strip edges, and a
rational nonzero-error example over an interval of scales. CI builds the
new candidates and consumers serially before certificates, then runs
`test/lean/KadiriPairedZeros.lean`. Axiom audit source:
`.research/DusartPairedZerosAxioms.lean`; logs:
`.research/dusart-{pair*,three-kernel-uniform,kadiri-paired-*}.log`.
All 14 new theorem exports audit only `propext`, `Classical.choice`, and
`Quot.sound`; the leaf chain and the new Lean regression compile.
The fast source/architecture profile, Ruff format/lint, mypy, workflow
lint, and all 89 Python tests passed for the proof increment. Ruby and
minitest are now installed locally: all 16 metadata tests (83 assertions)
and submission-mode metadata validation pass with no skips. The fast gate
now requires Ruby; regression tests prevent reinstating the skip.
No full-project CI success is claimed.

The conjugation/multiplicity bridge and central-strip sum integration
proposed at this stage are now proved; see the newer section above.
The numerical
Mossinghoff--Trudgian parameter choices and final `R=5.573412` are NOT yet
certified by this symbolic comparison. Do not weaken that target or restore
the discarded full record-gap replay. All three providers and the all-`k`
completion remain open. The older NEXT paragraph below is superseded.

### Full H2 and strict transform positivity (newest, 2026-09-22)

`KadiriLaplacePositivity.re_kadiriWeight_laplace_nonneg` now proves H2:
the actual scaled weight's transform has nonnegative real part for EVERY
`Re(s)>=0`, EVERY `pi/2<theta<pi`, and EVERY positive scale `eta`.
The imaginary axis is included. The stronger
`re_kadiriWeight_laplace_pos` proves strict positivity for `Re(s)>0`;
no small-scale bound or transform-positivity assumption is needed.

This is a direct energy proof, not an imported headline result:

- Mathlib-only `FiniteLaplace.VolterraEnergy` constructs the exponential
  primitive, proves its differential equation, and integrates the
  derivative of its squared norm.
- `IntervalIntegral.Triangle` proves triangular Fubini with a measurable
  indicator on a compact rectangle. `FiniteLaplace.Correlation` then
  identifies the actual overlap transform with a backward Volterra
  quadratic form. Its real part is exactly an endpoint square plus
  `Re(s)` times a square integral.
- The generic source may change sign. Strict positivity follows when
  it is nonzero at an interior point, using the differential equation.
  The actual cosine bump satisfies this at zero.
- `FiniteLaplace.Scaling` proves exact congruence, scalar multiplication,
  and oriented nonzero-real rescaling. The consumer applies these to
  the proved cosine-correlation identity and the actual clipped weight.

All 20 new exports pass axiom audits with only `propext`,
`Classical.choice`, and `Quot.sound`. Candidate and consumer builds,
the new arbitrary-parameter/boundary regressions, the earlier
`KadiriPositivity` regression, and all 88 Python tests pass.
CI builds the candidates and consumer serially and runs the new regression.
Logs: `.research/dusart-{volterra-*,triangle,laplace-*,correlation-scaling}.log`.

NEXT: prove the smoothed paired-zero inequality of Kadiri proposition 4.2
and the sharp gamma/zero-contribution estimates. The old `sigma>1`
Poisson-kernel Stechkin theorem is not this smoothed result. H2 and strict
positivity now discharge the transform-sign/denominator obligations.
A boundary rational-kernel comparison and a bounded analytic strip
minimum principle are the next non-certificate steps. All three global
Dusart providers and the all-`k` theorem remain open; do not redo H2.

### Weight positivity and sharp derivative/transform bounds (newest, 2026-09-22)

`KadiriCorrelation` proves the actual kernel's cosine-overlap integral
identity by exact integration, then nonnegativity throughout its support
for EVERY `pi/2<theta<pi`. `KadiriWeightPositivity.kadiriWeight_nonneg`
extends this to every real argument of the scaled compact weight, for
every positive scale. Neither result uses sampled numerical values.

`KadiriDerivativeBound` proves the sine-correlation identity for the
second derivative and the sharp bound
`|h_theta''(u)| <= -h_theta''(0)` on the ENTIRE support. The maximum is
formally attained at zero (`isGreatest_abs_kadiriKernel₂`). Its closed
value is `tan(theta)^2/cos(theta)^4 * (-theta/tan(theta)+cos(theta)^2)`.
The scaled bound is exactly `eta^3*(-h_theta''(0))`.

Mathlib-only `Integrals.CosineCorrelation` evaluates both overlap integrals;
`Integrals.CorrelationBound` proves the general finite-overlap square bound
using `2*|xy|<=x^2+y^2`, interval monotonicity, and translation. These
candidates are exported through the new `Integrals` facade and were
built independently before their consumers.

`KadiriLaplaceBounds` proves the complex pole-subtracted transform bound,
and the real error bound `eta^3*m(theta)/(x*(x^2+y^2))` for EVERY `x>0`.
`KadiriStechkin.kadiriWeight_master_nonneg` now discharges ALL weight-side
hypotheses in the master inequality. It and `kadiriWeight_explicitFormula`
use the sharp derivative constant, not an existential compactness bound.

Targeted builds and both actual-weight Lean regressions pass. The new
regression retains arbitrary admissible angles, positive scales, full
support points, complex evaluation points, and polynomial parameters.
All 19 new or modified proof exports pass axiom audits with only `propext`,
`Classical.choice`, and `Quot.sound`. All 87 Python tests pass, including
the extended serial CI build-order check. Logs are under
`.research/dusart-{correlation-*,cosine-correlation,kadiri-*}.log`.

NEXT: prove nonnegative real Laplace transform for `Re(s)>=0` (the paper's
H2), then the sharp zero-contribution and gamma bounds. Weight positivity
does NOT alone imply H2. A possible direct route is a Volterra energy
identity: if `Q'=q-s*Q` and `Q(a)=0`, then
`Re integral q*Q = |Q(b)|^2/2 + Re(s)*integral |Q|^2 >=0`.
Triangular Fubini must identify this with the kernel transform; neither
step is proved yet. The sharp zero-free/PNT estimates and finite analytic
inputs for all three global Dusart providers remain open. Do not repeat
the now completed correlation, derivative-maximum, or cubic-error work.

### Smoothed master inequality and actual paper weight (newest, 2026-09-22)

`SmoothedStechkinFormula` now proves the shifted explicit formula and
`smoothedStechkin_master_nonneg`, with the finite trigonometric sum moved
inside the actual xi divisor sum. Absolute summability is proved at every
complex point; multiplicities are retained. The master inequality applies
for every `sigma>1/2`, `delta>=0`, `kappa<=1` and nonnegative polynomial,
with the previously stated regularity and nonnegative-weight conditions.
It retains the exact gamma factor and boundary remainder, without assuming
an explicit formula or any of the subsequent sharp estimates.

The four `KadiriWeight*` modules construct the actual trigonometric kernel
from Kadiri section 2.2 and Mossinghoff--Trudgian section 2. They prove its
first two derivatives, continuity, positive support and value at zero,
and all required endpoint identities for EVERY `pi/2<theta<pi`.
The exact parameter `theta=185573/100000` is proved admissible. The compact
scaled weight is `eta*h_theta(eta*u)`, supported on `[0,d(theta)/eta]`.
Its regularity and an existential bound on the second derivative follow
from proved formulas and compactness. This existential bound is NOT the
sharp numerical bound still required below.

`kadiriWeight_explicitFormula` instantiates the complete real explicit
formula with this actual weight. Its ONLY hypotheses are the angle range,
`eta>0`, and `Re(s)>1/2`; every derivative, endpoint, support, and boundedness
obligation is discharged. The cubic test weight is not substituted for
the paper's weight.

Targeted builds and both Lean regressions pass. The tests exercise the
master inequality with a nonzero weight and polynomial, and the actual
paper weight at every positive scale and every point in the required
half-plane. All 32 new exports pass axiom audits with only `propext`,
`Classical.choice`, and `Quot.sound`; all 87 Python tests pass.
CI builds these leaves and consumers serially before the corresponding
regressions. Logs: `.research/dusart-{kadiri-*,stechkin-regression}.log`.

NEXT: prove nonnegativity of the actual weight on its full support and
the nonnegative real Laplace transform required by the zero estimates,
then sharp gamma/zero-contribution bounds. The autocorrelation of the
compact cosine bump is a promising route to both positivity and a sharp
second-derivative bound; that representation is NOT proved yet. The
sharp zero-free/PNT estimates and finite analytic inputs for the three
global Dusart providers still remain. Do not redo the now completed
explicit formula, master inequality, or weight regularity, and do not
confuse a compactness bound with the required explicit constants.

### Continued explicit formula on the required half-plane (newest, 2026-09-22)

`SmoothedRealExplicitFormula.re_smoothedVonMangoldt_explicitFormula` now
proves the complete real smoothed formula for EVERY `Re(s)>1/2`:

`Re V_f(s) = Re F_f(s-1) - sum_rho Re F_f(s-rho)`
`+ f(0)*(-log(pi)/2 + Re digamma(s/2+1)/2) + Re smoothedGammaRemainder(h,d,s)`.

The sum is over the actual xi divisor with multiplicities, and the gamma
remainder is exactly the boundary integral defined and evaluated below.
The theorem has NO xi-nonvanishing hypothesis and includes `s=1` and any
xi zeros in its domain. Its assumptions are only the interval regularity,
endpoint conditions, second-derivative bound, and compact support of the
weight used throughout this development. No explicit formula, contour
shift, or continuation premise is assumed.

The stronger complex theorem
`SmoothedEntireFormula.smoothedVonMangoldt_entire_explicitFormula`
holds at EVERY complex `s`, in terms of entire paired sums
`E_xi(s)=sum_rho (F_f(s-rho)+f(0)/rho)` and the analogous negative-even
pole sum `E_gamma(s)`. Its constant is
`f(0)*(logDeriv(xi)(0)+(log(pi)+EulerGamma)/2)`.

The proof closes the previous continuation and constant-cancellation gaps:

- Mathlib-only `FiniteLaplace.Differentiability` differentiates the finite
  integral under an explicit majorant, requiring only interval continuity.
  `PairedBounds` proves a uniform inverse-square bound on each parameter
  ball. `PairedSeries` constructs summable majorants including the finitely
  many near terms, then proves both absolute convergence and holomorphy.
  This is genuinely local-uniform convergence, not pointwise summability.
- `SmoothedPairedSums` specializes those results to both zero families.
  `SmoothedPrimeEntire` proves the prime side entire using its fixed finite
  support. `SmoothedPairedEvaluation` converts the original resolvent sums
  to paired sums. The identity theorem extends the proved right-half-plane
  identity to the entire complex plane.
- `ZetaXiDivisorReflection` constructs the equivalence `rho -> 1-rho`
  preserving each multiplicity index via analytic-order invariance.
  `ZetaXiHadamardConstant` uses this equivalence at `s=1` to prove
  `Re logDeriv(xi)(0) = -sum_rho Re(1/rho)` and hence the real resolvent
  formula wherever xi is nonzero. Taking real parts of the ENTIRE paired
  identity then removes the constant without excluding any xi zeros.

All 22 new exported proof/continuation declarations pass axiom audits
using only `propext`, `Classical.choice`, and `Quot.sound`. Targeted builds,
the expanded nonzero cubic regressions, and all 86 Python tests pass.
The regressions cover the entire complex identity at arbitrary `s`, the
actual real formula for arbitrary `Re(s)>1/2`, reflected multiplicities,
and differentiation for arbitrary finite interval endpoints.
CI builds the new candidates and consumers serially before these tests.
Logs: `.research/dusart-{continuation-*,smoothed-entire-formula,real-explicit-formula,laplace-*}.log`.

Next prove the quantitative compact-weight gamma and zero-contribution
estimates, then the sharp zero-free/PNT estimates and the finite analytic
inputs required by the three Dusart providers. The complete explicit
formula, its continuation, and the real Hadamard constant are now DONE;
older descriptions of them as missing below are historical. Do not redo
those steps or search for an assumed replacement. The global declarations
`wangCrapis_primeCounting`, `wangCrapis_thetaBounds`, and
`wangCrapis_shortInterval`, and therefore the all-`k` theorem, remain open.

### Actual gamma boundary identity (newest, 2026-09-22)

`SmoothedGammaBoundary.smoothedGammaRemainder_eq_neg_trivialZeroSum`
now proves, for EVERY `Re(s)>1/2`, the paper's exact complex boundary term:

`(1/(2*pi))*integral_t smoothedGammaIntegrand h d s t + F_h(s)/s^2`
`= -sum_{n>=1} (F_f(s+2*n)-f(0)/(s+2*n))`.

Its real part is Kadiri's `T_2`. The hypotheses are the existing interval
regularity, endpoint conditions, and bound on `f''`; no gamma identity,
contour shift, or finite truncation is assumed. `SmoothedGammaRemainder`
names this exact expression. `SmoothedRealDigammaIntegral` proves the
real-digamma contour evaluation, and `SmoothedDigammaReflection` kills
the reflected term by absolute interchange and inverse-Laplace support.
Mathlib-only candidates `Integrability.RightResolvent` and
`FiniteLaplace.RightResolventIntegral` prove the right-pole vanishing;
`Gamma.DigammaConjugation` proves the totalized conjugation identities.
The new `FiniteLaplace` facade exports its candidate subtree.

All 13 new exports pass axiom audits with only `propext`, `Classical.choice`,
and `Quot.sound`. Targeted builds and the nonzero cubic regression pass,
including the full boundary identity at EVERY symbolic `Re(s)>1/2` and
right-pole vanishing at `s=3/4+iy`, `rho=1+iv` for arbitrary heights.
CI builds the new candidates and consumers serially before this regression.
Logs: `.research/dusart-gamma-boundary{,-regression,-axioms,-fast}.log`.

The newer section above completes continuation of the explicit formula
below one and real Hadamard constant cancellation. Sharp estimates and
finite analytic inputs for the three global Dusart providers remain.
Do not repeat the now completed gamma-boundary or continuation work.

### Gamma pairing and the right-half-plane explicit formula (newest, 2026-09-22)

`SmoothedExplicitFormula.smoothedVonMangoldt_explicitFormula_of_one_lt_re`
now proves, for EVERY `Re(s)>1`,

`V_f(s)-f(0)*L(s) = R(s-1)-sum_rho R(s-rho)-sum_{n>=1} R(s+2n)`,

where `R(w)=finiteLaplace f d w-f(0)/w` and `L=-zeta'/zeta`. The nontrivial
zero sum uses the actual xi divisor with multiplicities. Inputs are the
existing interval regularity/endpoint conditions, a second-derivative bound,
and `f(u)=0` for `u>d`. The intermediate contour is chosen internally as
`c=(1+Re(s))/2`; no contour identity or explicit formula is assumed.

`DigammaHadamard` rewrites the checked PNT digamma expansion into genus-one
atoms at `shiftedGammaPole n=-2*(n+1)`, and proves their three-halves moment
from Mathlib's real p-series test. `DigammaHadamardIntegral` proves weighted
integrability and absolute interchange with cancellation of Euler's constant.
`SmoothedDigammaIntegral` then evaluates the actual smoothing weight against
each pole, giving exactly `-2*sum_n R(s+2*(n+1))`, and proves summability of
that remainder series. These gamma results hold on EVERY `0<c<Re(s)`.
`ZetaContourDecomposition` justifies splitting the actual zeta logarithmic
derivative into four integrable terms; the `log pi` constant cancels.
The xi modules also now expose integrability of the weighted logarithmic
derivative itself, as needed by this decomposition.

All 14 new exported theorems and the original
`Complex.hasSum_digamma_of_re_pos` pass axiom audits using only `propext`,
`Classical.choice`, and `Quot.sound`. The digamma source is Robby Sneiderman's
Apache-2.0 PNT module at locked revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`; no headline explicit formula
is imported. The nonzero cubic regression tests the gamma identity at
`s=3/4+iy`, `c=1/4` for every height, and the assembled formula at every
symbolic `s` with `Re(s)>1`. CI builds these leaves and consumers serially
before `test/lean/SmoothedInversion.lean`.
Logs: `.research/dusart-{digamma*,smoothed-digamma,zeta-decomposition,explicit-formula,formula-*}`.

The newer section above completes the paper's half-line gamma remainder
representation. Continuation of the entire explicit formula below one,
the sharp estimates, and finite analytic inputs for the three Dusart
providers remain. Do not substitute the proved `Re(s)>1` domain of this
explicit formula for the required one.

### Evaluated xi contour identity (newest, 2026-09-22)

`SmoothedXiInterchange.integral_finiteLaplace_mul_logDeriv_riemannXi_eq_remainders`
now proves, for EVERY `1<c<Re(s)`,

`(1/(2*pi))*integral_t R(s-c-it)*logDeriv(xi)(c+it) = sum_rho R(s-rho)`,

where `R(w)=finiteLaplace f d w-f(0)/w` and the sum uses the actual xi
divisor index, retaining multiplicity. Inputs are only the existing
interval continuity/derivative/endpoint conditions and a bound on `f''`.
No zero-line, interchange, contour-shift, or resolvent-pairing assumption
is supplied to this theorem.

The completed route is:

- `ThreeHalves`, `Integrability.Cauchy`, and `Hadamard.IntegralBounds`
  give the explicit fractional majorant. It allows different zero real
  parts bounded above by `B<c`, any positive `c`, and repeated indices.
- `Bochner.Series` and `Hadamard.Integral` give integrability of the
  entire weighted series and summability of its integrated norms. The
  relevant scalar/interchange patterns are adapted from the named Robin
  leaves at published Apache-2.0 revision
  `bfa72aec0c25c8ee29cefe4449d778ff30412bee`, with exact provenance in each
  candidate. The original line-location assumption is not imported.
- `XiHadamardIntegral` uses the actual critical-strip theorem and PNT's
  `IEANTN.RobinXiZeroSummability` at locked revision
  `f6147e7572ab3abe5428101bc0b13627bcb005df`. That 27-line fractional-moment
  theorem follows from order-one entire growth without RH.
- `FiniteLaplace.ContourBounds` converts the actual remainder bound to
  `C/|c+it|^2`, with explicit `C`, and cancels the Hadamard constant by
  inversion at zero.
- `Integrability.Resolvent` proves absolute two-variable Fubini via the
  exponentially decaying half-line representation of a pole.
  `FiniteLaplace.ResolventIntegral` then evaluates each regularized atom
  exactly as `R(s-rho)`, using inversion and the existing remainder-source
  Laplace transform. This does not require horizontal contour estimates.

All 28 new exported theorems and the PNT fractional moment pass the axiom
audit with only `propext`, `Classical.choice`, and `Quot.sound`. Regression
tests cover a positive contour below one, unequal and repeated zero real
parts, and the nonzero cubic smoothing weight: off-midline poles and the
actual evaluated xi identity hold for every tested symbolic height.
CI builds the candidates and consumers serially and runs
`test/lean/HadamardIntegral.lean` and `test/lean/SmoothedInversion.lean`.
Logs: `.research/dusart-{xi,smoothed-xi-interchange,laplace-resolvent,hadamard-regression}*`.

The next section added above completes the shifted gamma pairing and the
regularized explicit formula on `Re(s)>1`, followed by the half-line gamma
boundary identity on `Re(s)>1/2`. Continuation of the whole formula and the
sharp estimates needed by Dusart remain. The prime-side inversion and whole xi zero pairing must
not be redone. The three global Dusart providers and all-`k` theorem remain open.

### Absolute inversion and the actual prime contour identity (newest, 2026-09-22)

The right-hand contour identity is now proved, not supplied as a hypothesis.
`SmoothedPrimeIntegral.smoothedVonMangoldt_sub_logDeriv_eq_integral` gives

`V_f(s)-f(0)*L(s) = (1/(2*pi))*integral_t L(c+it)*(F(s-c-it)-f(0)/(s-c-it))`,

where `L=-zeta'/zeta`, `V_f` is the existing `smoothedVonMangoldt`, and
`1<c<Re(s)`. Its inputs are the interval continuity/derivative/endpoint
conditions already used for the Laplace remainders, a bound on the second
derivative, and vanishing of the actual weight beyond `d`. No inversion,
interchange, zero-free, or explicit-formula identity is assumed.

The Mathlib-only route consists of five candidates:

- `FiniteLaplace.RemainderSource`: the continuous source
  `f(max(0,min(d,u)))-f(0)`. It is zero for `u<=0`, equals `f(u)-f(0)`
  inside the interval, and equals `-f(0)` after `d` when `f(d)=0`.
  Its damped bilateral integral is exactly `F(s)-f(0)/s` for `Re(s)>0`.
- `Integrability.Cauchy`: integrability of `1/|s+it|^2` when `Re(s)!=0`.
  The scaling argument is ported from the named Robin leaf at published
  revision `bfa72aec0c25c8ee29cefe4449d778ff30412bee`; only Mathlib is imported.
- `FiniteLaplace.Inversion`: the exact Fourier transform, its absolute
  integrability, and inverse Laplace integral with the full `1/(2*pi)`
  normalization, for every positive line and every real evaluation point.
  Mathlib Fourier inversion requires only continuity of the source. No
  global first or second derivative of a zero extension is imposed.
- `LSeries.VerticalIntegral`: actual summability of integrated absolute
  Dirichlet-term norms and the resulting whole-line interchange. The term
  norms depend only on the real part of the contour.
- `FiniteLaplace.DirichletIntegral`: inversion at every `log n` and the
  resulting smoothing identity for any absolutely convergent Dirichlet
  series, including the zero-term convention. The project consumer
  specializes it to von Mangoldt and subtracts the original zeta series.

All 22 exported theorems pass the axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`. The regression uses the cubic weight
`1-3u^2+2u^3` through one, zero afterwards. It tests a nonzero inverse at
`u=2`, nonzero second derivative at zero, and the actual prime contour
identity at `s=2+iy`, `c=3/2`, for EVERY height `y`. CI builds each candidate
before its consumer and runs `test/lean/SmoothedInversion.lean` serially.
Logs: `.research/dusart-inversion-{source,build,fubini,dirichlet,regressions,axioms,fast,commit}.log`
and `.research/dusart-prime-integral.log`.

The subsequent evaluated xi contour identity above completes the zero-side
pairing with actual multiplicities and justified interchange. Gamma pairing
and continuation from `Re(s)>1` to the needed `Re(s)>1/2` remain. This still
does not establish the full smoothed explicit formula, its sharp numerical
estimates, the three global Dusart providers, or the all-`k` theorem. Do not
re-import the unproved explicit-formula headline or redo completed inversion.

### Gamma-integral convergence on the required half-plane (newest, 2026-09-22)

`DigammaLowerBound` proves `Re(psi(z)) >= -gamma` for `Re(z)>=1` directly
from the nonnegative real terms of the checked digamma series. Recurrence
gives `Re(psi(z)) >= -gamma-1/Re(z)` throughout `Re(z)>0`. Together with
the preceding explicit upper bound, this yields
`|Re(psi(1/4+it/2))| <= log(|t|+3)+|gamma|+5` for every real height.
It imports only `DigammaExplicitBounds` and the already-audited series leaf.

Two new Mathlib-only candidates compile independently:

- `FiniteLaplace.Continuity`: continuity of `F(s-it)` for a source continuous
  on `[0,d]`, with no global extension hypothesis or restriction on `Re(s)`;
- `Integrability.LogCauchy`: explicit domination of
  `log(|t|+c)/(a^2+(t-b)^2)` by a multiple of `(1+|t|)^(-3/2)`, and absolute
  integrability for all `a>0`, `c>=1`, and real `b`.

`SmoothedGammaRemainder` defines the actual second-derivative integrand of
Kadiri's `T2` term (before the `1/(2*pi)` factor), proves it continuous,
gives its explicit pointwise majorant, and proves it absolutely integrable
for **every `Re(s)>1/2`**. The source `h` need only be continuous and bounded
on `[0,d]`; later consumers instantiate it as the weight's second derivative.
This includes the below-one line required by the paper. The quantitative
bound retains the positive separation `a=Re(s)-1/2` and denominator
`a^2+(t-Im(s))^2`. It does not assume the explicit formula or any zero-free
region.

All 11 new exported theorems pass the axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`. `test/lean/SmoothedGamma.lean` checks
the nonzero cubic weight's second derivative `-6+12u`, convergence at
`s=3/4+it` for every height, the `c=1` logarithmic-kernel boundary case,
and the digamma bound at one. CI builds the candidates, then the consumers,
then this regression in serial order. Logs are
`.research/dusart-gamma-{build,regressions,axioms,fast,commit}.log`.

The remaining non-certificate obligation is still the **smoothed explicit
formula's contour/inversion identity and the justified exchanges**. Its
real zero sum and gamma integral now both have proved absolute convergence.
Next prove the identity, then the compact test-function estimates and sharp
numerical errors. The coarse gamma majorant here establishes convergence;
do not claim it establishes the sharp zero-free constant. The three global
Dusart providers and full all-`k` theorem remain unfinished.

Source route for the next identity: Kadiri section 3.1 first applies inversion
and a rectangular contour to `phi(y)=(f(0)-f(y))*exp(-s*y)` for `y>=0`,
zero for `y<0`, on `Re(s)>1`. Its transform is the negative of the already
proved pole-subtracted remainder. Then use the functional equation and
Hadamard cancellation, and justify continuation to `Re(s)>1/2`. Pointwise
convergence does not itself justify continuation or exchanging integrals.
Check the gluing hypotheses directly: `f'(0)=0` gives a continuous first
derivative for this `phi`, but arbitrary `f''(0)` does NOT give a globally
continuous second derivative. The paper's theorem 3.1 allows piecewise
regularity. Do not introduce `f''(0)=0` merely to use a stronger interface.

### Explicit Laplace remainders and convergent smoothed zero sums (newest, 2026-09-22)

Three independent Mathlib candidates under `Analysis/Complex/FiniteLaplace`
now provide the finite Laplace integral, the two integration-by-parts
identities with all endpoint terms, explicit remainder bounds, and indexed
summability. They compile using only Mathlib.

For a weight `f` on `[0,d]` with derivative `g`, second derivative `h`,
`f(d)=g(0)=g(d)=0`, and `|h| <= M`, the proved identity is
`F(s) = f(0)/s + F_h(s)/s^2` for every `s != 0`. The proved norm bounds are

- `|F(s)-f(0)/s| <= M*d*exp(max(0,-Re(s))*d)/|s|^2` on every line;
- `|F(s)-f(0)/s| <= M/(Re(s)*|s|^2)` when `Re(s)>0`;
- at `s-rho`, with `Re(rho)<=B` and `|rho|>2|s|`, the explicit majorant
  is `4*M*d*exp(max(0,B-Re(s))*d)/|rho|^2`.

Only continuity on the closed interval and derivatives in its interior
are required. Do NOT impose global continuity of the zero extension at
zero, which would force `f(0)=0`. Nor require `tsupport f` to lie in
`[0,d)`: that excludes weights nonzero arbitrarily close to `d`, despite
their value vanishing at `d`. The interval formulation allows the actual
paper's endpoint behavior.

`SmoothedXiRemainder` specializes the indexed comparison to the actual xi
divisor with multiplicity. For EVERY complex `s`, it proves summability of
the shifted inverse-square weights, the real resolvents, and the complex
pole-subtracted Laplace terms. If `f(0)` is real, it additionally proves
absolute convergence of `sum_rho Re(F(s-rho))`. No RH assumption, real-part
restriction on `s`, simplicity assumption, or supplied zero enumeration is
used. This does not claim absolute convergence of the unregularized COMPLEX
sum, which is not generally available.

Primary source: [Kadiri, section 3.1 and the bounds following it](https://www.cs.uleth.ca/~kadiri/articles/zeta-acta-04-09-07.pdf).
The IBP and far-zero comparison patterns were checked in the pinned PNT
`Kadiri.laplaceTransform_ibp` and
`Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq`.
The candidate documentation records that provenance. The parent `Kadiri`
module is NOT imported: its full explicit formula still has unproved
inputs. Robin's reviewed weighted explicit formula assumes RH and cannot
be substituted for the unconditional identity needed here. The sibling
catalog and the Robin/BV/WIP transform interfaces have been checked for this
step; do not repeat a broad search for an existing complete Dusart theorem.

The next non-certificate obligation is still the **smoothed explicit
formula**, relating `smoothedVonMangoldt` to the Laplace pole term, this
now-convergent real zero sum, the gamma term, and the second-derivative
gamma integral. Prove its contour/inversion identity and exchanges, then
its quantitative errors and the actual compact test-function estimates.
Do not treat convergence alone as proving the explicit formula. The
three global Dusart providers and full all-`k` theorem remain unfinished.

Logs: `.research/dusart-laplace-{basic,bounds,summability,regressions,axioms,fast}.log`
and `.research/dusart-smoothed-xi.log`. The 16-export axiom audit lists only
`propext`, `Classical.choice`, and `Quot.sound`. The polynomial regression
uses the nonzero weight `1-3t^2+2t^3` on `[0,1]`, checks both half-plane
bounds, and instantiates convergence over actual xi zeros. CI builds the
three candidates before the consumer and runs that regression. Python
checks now include 80 passing tests; no certificate or dependency cache
rebuild was needed for this work.

### Stechkin pairs, the full xi sum, and compact smoothing (newest, 2026-09-22)

`Mathlib/Analysis/Complex/Poisson/Stechkin` proves the paired-kernel
inequality with coefficient `1/sqrt(5)` and the canonical shifted line
`tau = (1 + sqrt(1 + 4*sigma^2))/2`. It also proves that at a zero's height
the paired difference retains `1/(sigma-beta)`. The statements cover the
whole closed strip `0 <= beta <= 1`, for every `sigma > 1` and every height.
The proof clears positive denominators and factors their difference into
nonnegative polynomials; it contains no numerical replay.

`Mathlib/NumberTheory/LSeries/ZetaTrigonometricShift` proves positivity
for an arbitrary nonnegative cosine polynomial with nonnegative weights,
subtracting `kappa <= 1` times the series at a right-shifted line. The
weighted theorem assumes summability, NOT `sigma > 1`. Its finite-support
and logarithmic-cutoff lemmas discharge summability for compact smoothing
at every complex point. The separate unweighted zeta logarithmic-derivative
specialization does correctly require `sigma > 1`.

`StechkinBasic` connects the real kernels to actual xi zeros and exports
`smoothedVonMangoldt` and compactly smoothed positivity. `ZetaXiStechkin`
then proves the FULL multiplicity-carrying sum inequality
`Re(logDeriv xi(sigma+it)) - Re(logDeriv xi(tau+it))/sqrt(5) >= 0`.
It does not assume a zero-pairing bijection. Instead it subtracts the
Hadamard expansions at `s` and `1-conj(s)`. The constant cancels, xi's
symmetries give twice its real logarithmic derivative, and the absolutely
convergent difference is exactly the paired kernel. The old Hadamard
identity is generalized to every nonzero xi value; its old right-half-plane
API remains available unchanged.

`ZetaXiStechkinZero` retains the FULL pole `1/(sigma-beta)` for an actual
zero with `beta > 1/2`. It uses global xi conjugation symmetry to obtain
the reflected zero and proves that the two divisor indices are distinct.
Keeping both equal paired terms cancels the factor two in the Hadamard
identity. Neither zero is assumed simple. The condition `beta > 1/2` is
intentional: a zero on the midline is its own reflection and cannot be
silently counted twice by this argument.

Primary references checked for this step:

- [Kadiri, Lemma 2.1](https://www.cs.uleth.ca/~kadiri/articles/zero-free-region-Dedekind-June07-2011.pdf)
  states the paired and aligned kernel inequalities proved here.
- [Mossinghoff--Trudgian, sections 2--4](https://arxiv.org/pdf/1410.3926)
  uses COMPACT SMOOTHING inside the critical strip and explicit error
  estimates to obtain the sharper region. The classical unweighted
  Stechkin argument alone does NOT establish its constant `R = 5.573412`.

Next obligations: derive the smoothed Laplace explicit formula and its
quantitative gamma/zero-sum errors, construct and bound the paper's compact
test function, and establish the numerical zero-height inputs. No separate
multiplicity reindexing is needed for the full-sum nonnegativity theorem.
The three global Dusart providers are still unfinished.

Both candidates build independently before the project consumers. The new
`test/lean/Stechkin.lean` tests the closed-strip boundary, aligned pole,
full-sum identity/positivity, the full single-zero coefficient for `beta > 1/2`,
and a nonzero compact weight at `sigma = 1/2`.
CI builds these analytic targets serially before the regression. Logs are
`.research/dusart-stechkin-{candidates,basic,regressions,axioms,fast}.log`
and `.research/dusart-xi-stechkin.log`. No certificate was replayed, no
dependency revision changed, and no cached build files were removed.

Verification: all new analytic modules and both Lean regression files pass.
The 24-export axiom audit lists only `propext`, `Classical.choice`, and
`Quot.sound`, including the whole zero sum and its full single-zero pole.
Ruff formatting/lint, mypy, actionlint, and 79 Python tests pass. The fast
source checks pass; Ruby metadata validation remains skipped locally.
The additional single-zero build log is `.research/dusart-stechkin-zero.log`.

### Actual zero contributions and the explicit classical constraint (newest, 2026-09-22)

`ZetaXiZeros` proves that every actual xi zero lies in `0 ≤ Re(ρ) ≤ 1`.
The shifted-gamma product now also covers `Re(s)>0`, `s≠1`, so xi/zeta
zero equivalence on that domain is available without a supplied hypothesis.

`ZetaXiZeroContribution` proves:

- every actual xi zero occurs in the multiplicity-carrying divisor index;
- the Hadamard sum has constant `logDeriv riemannXi 0`, identified by
  evaluating the degree-one factorization at zero;
- all real summands are nonnegative to the right of the critical strip;
- retaining a zero `β+iγ` gives the negative term `-1/(σ-β)` in `Re(-ζ'/ζ)`;
- the constant is exactly `(log(4*pi) - EulerGamma - 2)/2`.

`ZetaZeroFreeInequality` combines these results with the proved pole, gamma,
and `3,4,1` positivity estimates. `xi_zero_three_four_one_constraint` is an
unconditional explicit necessary inequality for every actual xi zero;
`riemannXi_ne_zero_of_three_four_one` excludes a proposed zero when its
elementary reverse inequality holds. This is NOT yet a numerical zero-free
region meeting Dusart's constants. Do not treat a weaker classical region
as establishing the published fixed-cutoff theta estimates. Sharper
polynomial/Stechkin estimates and the zero-sum error argument remain needed.

The full required PNT Hadamard dependency now compiles. Its only blocking
errors were five Lean 4.34 API edits in four files: `logDeriv_fun_mul`, two
uses of `Finset.prod_le_prod₀`, and two explicit `-1 ≤` premises for positive
logarithms. `scripts/patch_pnt_compat.py` records these edits, verifies the
exact locked revision and original Git objects, validates every target
before writing any, refuses unrelated edits, and is idempotent. CI applies
it before Lean builds; `CONTRIBUTING.md` gives the local command. The four
modified files in `.lake/packages/PrimeNumberTheoremAnd` are intentional,
reproducible compatibility ports, not unrelated work to discard. No cache
was deleted and no theorem statement was changed.

The root `lakefile.toml` revision now matches BOTH existing lockfiles and
the tested checkout (`f6147e7572ab3abe5428101bc0b13627bcb005df`). The old
configuration alone had a different revision, making later `lake update`
select a different source tree. No dependency update or new revision was
introduced by aligning it.

The three new modules, expanded Lean regression, and twelve-export axiom
audit pass. This includes the imported Hadamard factorization, summability,
and exact constant; every audited declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`. Fast checks, Ruff, mypy, actionlint,
and 78 Python tests pass (Ruby metadata validation is skipped locally). Logs are
`.research/dusart-xi-{zeros,contribution,zero-axioms,zero-regressions,zero-fast}.log`
and `.research/dusart-zero-free-inequality.log`. The three global Dusart
providers and final all-`k` theorem remain unfinished.

### Explicit gamma term and the xi bridge (newest, 2026-09-22)

`DigammaExplicitBounds` proves the explicit bound
`Re digamma(z) ≤ log(N+1) + ‖z-1‖/N` whenever `Re(z) ≥ 1` and `N ≥ 1`.
It uses the convergent series from the pinned dependency, estimates the head
by a harmonic number, cancels Euler's constant, and bounds the tail by its
inverse-square majorant. The explicit choice `N = max 1 ⌈‖z-1‖⌉` gives
`Re digamma(z) ≤ log(‖z-1‖+2) + 1`.

For `0 ≤ Re(s) ≤ 2`, the zeta gamma term is consequently bounded by
`(1/2) log(|Im(s)|/2+3) + 1/2 - (1/2) log(pi)`.
The coefficient, additive constant, and domain are explicit; this does not
use an existential big-O estimate.

`ZetaXiLogDerivative` proves the shifted-gamma product representation for
the actual entire `Complex.riemannXi`, then differentiates it on `Re(s)>1`.
Its final inequality bounds `Re(-ζ'/ζ)(s)` by the pole contribution plus the
gamma bound minus `Re(logDeriv riemannXi s)`. No supplied Hadamard identity
is required by these declarations. The new modules compile independently
(3.7 and 4.4 seconds respectively), and CI builds them before the expanded
`ZetaZeroFreeIngredients` regression.

The pinned sibling's `IEANTN/HadamardLogDerivative` fails to elaborate at
lines 130 and 210 because the current Mathlib distinguishes pointwise-product
and lambda-product rewrites. It is NOT imported by the new bridge. The
small required algebra is ported using `logDeriv_fun_mul`; the source and
revision are attributed in the module. No dependency checkout was edited.
The independently checked `DigammaSeries` and `CompletedXi` primitives are
the only new sibling imports.

Verification: the expanded Lean regression passes. All eight new exported
theorems and the three audited dependency primitives use only `propext`,
`Classical.choice`, and `Quot.sound`. Fast source checks, Ruff, mypy,
actionlint, and 72 Python tests pass. The Ruby metadata validator is skipped
locally because Ruby is absent. Diagnostic logs are
`.research/dusart-digamma-{build,regressions,axioms,fast}.log` and
`.research/dusart-xi-build.log`.

The individual zero's negative contribution and the exact constant have
now been connected and audited, as described above. The remaining task is
to derive the quantitative region and error estimates needed by the paper.
The classical trigonometric inequality, unit pole bound, and explicit gamma
bound are now available, but a quantitative zero-free region with constants
sufficient for Dusart's prescribed cutoffs is NOT yet proved. Neither are
the required zero sums, finite zero data, and three global Dusart providers.

### Zeta positivity and the explicit pole (newest, 2026-09-22)

`Mathlib/NumberTheory/LSeries/ZetaTrigonometric` proves the general
nonnegative-cosine-polynomial inequality for real parts of `-ζ'/ζ`, including
the classical `3 + 4 cos u + cos(2u)` instance. It also proves that the norm
of `-ζ'/ζ` in `Re(s) > 1` is bounded by its value on the real axis. This uses
only the absolutely convergent von Mangoldt series from Mathlib, not a
zero-free theorem with an unproved input.

`ZetaRealPole` differentiates the existing fractional-part Abel integral
using the pinned `PrimeNumberTheoremAnd` dominated-differentiation primitive.
The signed derivative kernel is nonpositive on the real axis. This proves,
for every `σ > 1`, `Re ζ(σ) ≥ 1/(σ-1)` and
`Re (-ζ'/ζ)(σ) ≤ 1/(σ-1) + 1`. The norm bound
`‖ζ'/ζ(s)‖ ≤ 1/(Re(s)-1) + 1` follows throughout `Re(s) > 1`.
The separate bound `‖ζ(σ)‖ ≤ 1/(σ-1) + 1` improves the existing
`zetaNear1BndExact_explicit` witness from 3 to 2 on `(1, 2]`.
The old constant-3 public statement is preserved as a consequence.

Next analytic work: connect the Hadamard logarithmic derivative to a
negative contribution from an individual nontrivial zero. The explicit
gamma-factor bound has now been proved as described above. The pinned dependency's
`Mathlib/NumberTheory/LSeries/RiemannZetaHadamard` and
`IEANTN/HadamardLogDerivative` contain relevant factorization/algebra
primitives; their quantitative zero-free conclusion is not being assumed.
The current log-power-nine strip and eventual MediumPNT still do not give
Dusart's numerical starting points. Bounds on the zero sums in the explicit
formula and the finite zero/prime data remain necessary afterwards.

Source investigation also found Dusart's correction to the later smoothed
psi formula, including the corrected `B5` expression. Use the corrected
formula if developing that route:
https://www.unilim.fr/pages_perso/pierre.dusart/Recherche/correctif_RJ.pdf
His 2022 HDR, Chapter 2, gives the large-range argument in detail:
https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf
The new lemmas do not claim that either full error theorem is proved.

CI builds these ingredients and runs `test/lean/ZetaZeroFreeIngredients.lean`
in the non-certificate foundations job. The candidate and `ZetaRealPole`
compile, the regression examples pass, and the eight audited exports use
only `propext`, `Classical.choice`, and `Quot.sound`.
The updated `ZetaExplicitBounds` consumer also compiles. Fast source checks,
Ruff, mypy, actionlint, and 71 Python tests pass; the local fast gate skips
the Ruby metadata validator because Ruby is not installed.

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
