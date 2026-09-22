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

### Exact averaged powers and zero-free damping (newest, 2026-09-22)

The box-transform evaluation from the preceding section is now proved.
`DusartBoxDistributionIntegral` proves the weighted-step Fubini identity
for every averaging order, including the discontinuous order-zero case.
The real and complex primitive-transform modules perform the exact
exponential substitution using only regularity on the positive interval.

`DusartBoxPowerTransform` proves, for every nonzero complex `s`,
`F_w(-s)+1/s = average(t^s/s)`. `DusartBoxMainTerm` specializes this to
`F_w(-1)=x+(m+3)*h/2-1`. The new spectral formula substitutes both identities
into the actual averaged psi error and retains the complete xi series,
negative-even series, endpoint constant, and lower-endpoint correction.
The averaged xi powers are absolutely summable by the existing paired
series theorem; no divergent reciprocal series is separated out.

BV's Mathlib-only `norm_real_cpow_div_le_exp_gap_mul_reciprocal` is now
adapted in `Mathlib/Analysis/SpecialFunctions/Pow/ComplexDecay.lean`, with
the reviewed SHA and attribution. `DusartBoxZeroBounds` applies it on the
entire box support. `DusartBoxSpectralFormula` assembles the bound for any
finite selection of the actual multiplicity-counted xi zeros. This is a
conditional quantitative bound given a real-part gap, not an assertion
that the required low-height gap or RH has been established.

Next analytic obligations: the stronger height decay from repeated
averaging (finite differences), the explicit high-zero tail estimates,
the negative-even correction budget, and the required low-height input.
Then certify the scalar budgets at the fixed cutoff. Mere summability
or the finite-selection bound is not a numerical bound on the whole
zero series. The three final Dusart providers and all-`k` conclusion
remain unfinished. Do not reconstruct the contour or explicit formula,
repeat the sibling audit, or restart any legacy full-gap certificate replay.

Verification: all ten new modules compile; nineteen new Lean examples
and five preserved explicit-formula examples pass. All twenty-six audited
exports use only `propext`, `Classical.choice`, and `Quot.sound`.
CI builds the candidate leaves and consumers serially before their tests.

The preceding CI run `35795818995` failed because the real Gamma regression
ran before `KadiriGammaBudget` had been built. The workflow now runs that
test immediately after its dependency. A fast Python check walks the owned
transitive imports for every foundation test and rejects missing preceding
builds; its negative regression reproduces the reported missing artifact.

### Actual box cutoff and averaged explicit formula (newest, 2026-09-22)

The cutoff and arithmetic-identification obligations in the previous
smoothing section are now proved. The new Mathlib-only regularity leaf
shows that `m+1` interval averages of any monotone function are `C^m`,
using the continuous primitive and FTC. Separate support and finite-sum
identities preserve locality, translations, and arithmetic finite sums.

`DusartBoxCutoff` averages the unit step `m+3` times for arbitrary natural
`m`, then composes with `x-exp(u)`. The weight is globally `C^2`, lies in
`[0,1]`, equals one at zero for `x>=1`, and is zero at and beyond the
exact endpoint `log(x+(m+3)*h)`. Continuity includes the precise lower
distribution boundary; no zero-measure corner is silently discarded.

`DusartBoxPrimeSum` identifies the actual Chebyshev average with a fixed
finite von Mangoldt sum and hence with `smoothedVonMangoldt weight 0`.
`DusartBoxExplicitFormula` discharges every regularity, endpoint, and
bounded-derivative premise of the already-proved entire explicit formula.
The endpoint derivatives vanish by Mathlib's local-extremum theorem.
`DusartBoxAverageFormula` combines these proofs into the exact unconditional
identity for `dusartPsiAverageError (m+3) h x`, retaining all xi, negative-even,
and constant terms. There is no RH, zero-location, or assumed formula input.
All seven new modules compile. The 23 new regression examples and eight
preserved smoothing examples pass; all 27 audited exports use only
`propext`, `Classical.choice`, and `Quot.sound`.

Still needed for the quantitative Dusart estimate: evaluate or bound the
box weight's finite Laplace transform (including its main term), bound the
resulting actual zero contributions, prove the required low-height input,
and certify scalar parameters at the fixed cutoff. The exact identity does
not by itself prove the numerical error theorem or the final three providers.

### Pointwise recovery from iterated psi averages (newest, 2026-09-22)

The monotone smoothing step of Dusart's HDR (2022), section 2.2,
Theorem 35, is now formalized for every natural averaging order.
`IntervalIntegral.IteratedAverage` proves the support enclosure for any
monotone function, without assuming continuity at its jumps, and the exact
identity subtracting the linear main term. `DusartPsiSmoothing` applies
Mathlib's `Chebyshev.psi_mono` to obtain the two-sided pointwise error and
the normalized loss `m*delta/2` at smoothing width `x*delta`.
The independent candidate and its actual psi consumer compile; eight
regression examples pass and all eight audited exports have only the
three standard logical axioms.

This interface averages `psi(t)-t` directly. It does not discard the
logarithmic/trivial-zero terms: a later explicit-formula evaluation must
include them in the bounds on both adjacent averages. The next analytic
obligations are that actual averaged explicit formula, its zero-sum
estimates, and the fixed-cutoff numerical error bound. The smoothing
theorem alone is not a Dusart provider or a numerical PNT estimate.

### Elementary correction budget and all-degree moments (newest, 2026-09-22)

The mass-substitution obligation in the older grid section is now closed.
`KadiriConservativeBudget` drops the nonnegative finite reciprocal mass,
uses Mathlib's proved `eulerMascheroniConstant_lt_two_thirds`, and proves
monotonicity of the complete correction in the resulting tail constant.
`KadiriConservativeBootstrap` transports both its sign and every grid
margin into the actual region theorem with the correct inequality direction.

`KadiriElementaryMoments` reuses the already-proved full-support bound
`abs_kadiriKernel₂_le_neg_zero` and Mathlib's monomial integral. For every
natural degree `j` the actual absolute derivative moment is bounded by
`(-kadiriKernel₂ theta 0) * support^(j+1)/(j+1)`. No quadrature is required.
`KadiriElementaryBootstrap` substitutes these proved bounds for all four
moment inputs. Thus no finite zero-mass sum, Euler-constant evaluation, or
absolute-derivative integration remains in its numerical endpoint budget.

All four new modules and their actual bootstrap consumers compile. The
eleven audited declarations, including Mathlib's Euler bound and the actual
elementary region theorem, use only the three standard logical axioms.
CI builds the new leaves and consumers serially before their regressions.

Exploratory floating-point calculations retain positive sixteen-band trial
margins along the recorded chain even with the looser elementary moment
envelope (about `2316.89`, versus the sampled mass `768.53`). This is only
feasibility evidence, not a numerical certificate or a verified region.

Still open: scalar admissibility and margin certificates, coefficient signs,
the actual low-height zero-location input, and the explicit zero-free-region
to Chebyshev-error proof at the required cutoff. The latter is genuine
non-certificate analysis, not supplied by the existing existential medium-PNT
bound. The three final Dusart providers and the all-`k` result are not closed.
Preserve the non-certificate-first priority; do not repeat the broad sibling
audit or restore any full record-gap replay dependency.

### Arbitrary covers and uniform scale grids (newest, 2026-09-22)

The scale-cover assembly requested below is now implemented.
`KadiriScaleCoverBootstrap` applies the actual sharp band theorem on any
cover of `(0,eta0]`. Each interval supplies its lower scale, upper scale,
and height threshold; the threshold may be bounded either by the base
height or by the exponential forced by the previous region. The proof
covers the full critical strip and both signs of the ordinate.

`KadiriGridBootstrap` supplies the cover for every positive band count
`m`, directly reusing Mathlib's `Monotone.biUnion_Ico_Ioc_map_succ`.
Its intervals are `(eta0*j/m, eta0*(j+1)/m]`; exact grid boundaries and
the final endpoint are included. The correction multiplier simplifies to
`j/m`. There is no remaining real-scale coverage obligation in this API.
The original `KadiriSplitBootstrap` is now a two-member specialization of
the same proof, preserving its mathematical statement.

The new grid API supports the positive sixteen-band trial margins recorded
below, but those trials remain uncertified. It does not supply the numerical
moment bounds, coefficient signs, static admissibility, low-height zero
information, or the final Dusart provider proofs. Those obligations must
not be replaced by the sampled numerical evidence.

One further analytic substitution is needed before certifying those trial
budgets: the probe drops the nonnegative `xiLowReciprocalMass H`, while
`kadiriTailAffineConstant` still retains its exact subtraction. Prove the
resulting upper bound through the quadratic and cubic correction terms,
using `re_xi_divisor_reciprocal_nonneg` and the already-proved nonnegative
derivative mass and kernel constants. This can avoid a separate numerical
low-zero mass sum; it does not remove the low-height location hypothesis.

### Sharper zero-harmonic Gamma estimate (newest, 2026-09-22)

`DigammaRealBounds.re_digamma_ofReal_le_log` proves `Re(digamma(x))<=log(x)`
for every positive real `x`, using Mathlib's decreasing sum--integral
comparison and the existing actual PNT digamma-series limit. Its consumer
`SmoothedGammaRealBounds` removes the first upper error from the shifted
Gamma factor at zero height. The actual `smoothedGammaFactorError` now has
zero branch `kappa/(sigma+2)`, instead of `(1+kappa)/(sigma+2)`. Nonzero
heights retain the two-error minimum. The residual, correction polynomial,
and actual region bootstrap consume this changed definition directly.
Comparison to the previous error now explicitly requires `sigma>=-2`;
the working region already satisfies the stronger `sigma>1/2`.

Exploratory, non-certified quadrature still finds a negative near-final
margin with only two scale regimes. A uniform cover by 16 scale bands,
using both the improved height and the retained correction on each band,
gives positive trial margins along the chain
`56 -> 8 -> 6.5 -> 6 -> 5.7 -> 5.59 -> 5.58 -> 5.575 -> 5.573412`
at `T=3.06e10`; the last tested margin is approximately `0.02035`.
These numbers are not rigorous certificates and do not establish a region.
The arbitrary-cover assembly is now supplied by the newer section above.
Numerical admissibility, moments, low-height zero data, and the final Dusart
providers remain open.

### Single-crossing minimum and two-scale bootstrap (newest, 2026-09-22)

The loose separated-transform bound is no longer necessary.
`KadiriTransformMinimum` proves, for positive `a0,a1`, that `K(w)` on
`[l,r]` is bounded below by `min(K(l),K(r))`. The actual source has one
sign change at `log(a1/a0)`. Its derivative transform can never become
positive after becoming nonpositive, so an interior minimum is excluded.
This is NOT a claim that `K` is monotone; both exact endpoint values remain.

The independent candidates `Deriv.EndpointMinimum` and
`FiniteLaplace.SingleCrossing` prove the general facts. Differentiation
directly reuses `hasDerivAt_finiteLaplace` and its real-part interface.
No new differentiation-under-integral argument or moment quadrature is needed.

`KadiriBootstrapMaster` now has a shared actual-transform band theorem,
with the old interface preserved and a new sharp endpoint-minimum variant.
`KadiriSplitBootstrap` connects that sharp variant to two scale regimes:
small `eta<=eta1` uses a higher threshold `T1<=exp(1/(R*eta1))`; the
other regime retains `(eta1/eta0)*C(eta0)`. Both signs of the ordinate,
the entire critical strip, and the equality case at the split are covered.
It retains the conservative `z=-1` mass parameter and all actual low-height,
previous-region, admissibility, and moment/endpoint budget hypotheses.

The new candidates and actual split theorem compile. The 13 new regression
examples and 74 preserved transform, bootstrap, polynomial, and moment
examples pass. All 13 audited new/compatibility exports use only `propext`,
`Classical.choice`, and `Quot.sound`. CI builds the candidates before the
master and split consumer serially, and runs the new tests.

Numerical feasibility is still an obligation. An exploratory quadrature
probe of the existing envelopes, even replacing the finite reciprocal-mass
subtraction by zero, suggests a feasible `56 -> 50` warm-up. A direct
`5.7 -> 5.573412` jump fails the tested margins. More importantly, the
tested `5.5735 -> 5.573412` step also has negative margin (about `-0.046`)
with the current conservative Gamma envelope, so merely adding iterations
is not a demonstrated solution. The zero-harmonic Gamma error remains
coarse; a one-sided real digamma upper bound is a concrete next analytic
improvement to investigate using the already-proved series and limits.
Do not present these probes as verified numerical iterations.
Low-height inputs, final Dusart providers, and all-`k`
completion remain open. No certificate replay was performed here.

### Exact polynomial and uniform height-ray bootstrap (newest, 2026-09-22)

`MossinghoffTrudgianPolynomial` now defines the degree-sixteen generating
sequence from table 5 of arXiv:1410.3926 as exact rationals and recomputes
its normalized autocorrelations. It does not equate these coefficients
with the paper's separately rounded cosine column. The zero coefficient
is exactly one, the normalization is positive, and global nonnegativity
at every real phase follows from a proved sum-of-squares identity.
Coefficient signs, `a1>a0`, and numerical bounds on their total remain
to be verified. Do not infer coefficient signs from phase nonnegativity.

The Mathlib-only `Trigonometric.Autocorrelation` candidate supplies the
general identity and the efficient positive-frequency formula
`2 * sum_{j<n-k} c[j]*c[j+k]`. The finite arithmetic can therefore use
one short row per frequency, not expand the defining double sums.
`Log.AffineRatio` proves the paper's needed monotonicity of
`log(t)/log(n*t+H)` for `n>=1`, `H>=0`, and `t>1`.

`KadiriBootstrapParameters` chooses `sigma(t)=1-1/(R*log(n*t+H))` and
derives the harmonic cutoff, increasing real coordinate, endpoint scale,
and fixed transform interval. `KadiriUniformBootstrap` applies these to
the actual moment-budget theorem. Its conclusion covers every divisor
zero with `abs(imaginary part)>=T`, both signs and the entire critical
strip. Conjugation reuses the existing multiplicity-preserving equivalence.
It uses the conservative mass parameter `z=-1` and the transform interval
`[(r/R)*log(T)/log(n*T+H), 1]`; sufficient numerical margins for this
box have NOT been demonstrated. An exploratory, non-certified quadrature
check finds this box insufficient near the target constant. The sharper
`xi_zero_gap_of_moment_band_budget` now retains the negative endpoint
correction on a scale band: `C(eta) <= (eta1/eta0)*C(eta0)` when
`eta1<=eta<=eta0`. This follows by monotonicity of `C(eta)/eta`, not an
unproved assertion that `C` decreases. Its zero-lower-scale specialization
preserves `xi_zero_gap_of_moment_budget` unchanged.

For the small-scale branch, `kadiriBootstrapHeightLower_of_small_scale`
derives `t>=exp(1/(R*eta1))` from the PRIOR region when `eta<=eta1`.
Here `eta` is the actual zero gap; do not replace `R` by the target
constant `r` without another argument. Combine this higher threshold with
the proved transform interval bounds, refining intervals or proving the
needed signed-transform monotonicity before final numerical verification.

The remaining inputs are explicit: admissible static parameters, four
moment bounds and exponential endpoint, actual low-height locations,
the previous region, and the correction/transform endpoint budgets.
The proved initial region is still `R=56`, not `5.7`. The three final
Dusart providers and the exact all-`k` conclusion are still unfinished.

Both independent candidates, their consumers, the uniform actual bootstrap,
and the candidate facade compile. The 20 new regression examples pass,
as do the 20 moment and 14 bootstrap regressions. All 26 audited new
theorem closures use only `propext`, `Classical.choice`,
and `Quot.sound`. CI builds these modules serially in `lean-foundations`,
before certificate jobs, and runs the new regression file.

### Uniform correction envelope and target-gap bootstrap (newest, 2026-09-22)

`XiLehmanAffine` bounds the actual positive-height majorant by
`A*log(t)+B` for `t>=T>=2`, `H>=4`. The explicit coefficients are
`A=1/(pi*H)+1/(2*pi*T)+8/H^2` and
`B=(H/T)*(1/(pi*H)+8/H^2)+4/(T*H)`. It does not assert that the tail
decreases with height. `KadiriTailEnvelope` sums this bound at arbitrary
natural harmonics, keeping the exact zero-height low-mass subtraction.
It also proves pole monotonicity and the needed nonnegative tail signs.

The Gamma residual now has proved monotonicity in the real coordinate as
well as in positive height. `KadiriMomentEnvelope` consequently uses the
fixed lower corner `(sigma0,T)`, independent of the moving `sigma`.
Its derivative-mass substitution directly invokes the existing four-moment
theorem. `KadiriCorrectionEnvelope` absorbs logarithmic terms using a stated
upper bound `eta*log(t)<=q`, yielding the full cubic correction bound with
the signed linear term intact.

`KadiriCorrectionSign` proves the quadratic and cubic coefficients are
nonnegative under the actual hypotheses. Factoring out the positive scale
reduces nonpositivity of the whole correction to its maximum-scale budget.
`xi_zero_gap_of_moment_budget` in `KadiriBootstrapMaster` connects this to
the actual xi zero. If the target gap already holds it returns it; otherwise
its failure supplies `eta*log(t)<=1/Rnext`. Thus this crucial upper bound
is not inferred incorrectly from the previous region's lower bound.

The resulting theorem still requires verified four-moment bounds, the
exponential endpoint inequality, a nonpositive explicit endpoint budget,
the closed-transform endpoint margin, and the existing polynomial,
admissibility, and low-height inputs. Their numerical feasibility has NOT
been certified. All three final Dusart providers remain open. Next, choose
and justify the paper's polynomial and admissible parameter ranges, bound
the remaining fixed inputs, and verify the iterations from the proved
starting constant `56`, not an assumed `5.7`.

All five new modules and the actual bootstrap compile. The 20 new moment
examples and 65 preserved bootstrap, transform, Gamma, and initial-region
examples pass. All 20 audited theorem closures use only `propext`,
`Classical.choice`, and `Quot.sound`. The fast source checks pass; no
certificate replay or numerical-region verification is claimed.

### Exact elementary transform and interval margins (newest, 2026-09-22)

`KadiriTransformClosedForm` now proves the actual `K(w,theta)` equals a
closed expression in real arithmetic, exponentials, sine, and cosine.
The two purely exponential terms include their removable zero-exponent
values, so both `w=0` and `w=1` are covered. The oscillatory denominators
are nonzero throughout the actual theta domain. No numerical integration
or transform identity is left as a hypothesis.

The Mathlib-only candidates `Integrals.ExpLinear` and `Integrals.ExpTrig`
reuse Mathlib's `integral_exp_mul_complex`, the FTC, and real/imaginary-part
integration. The new work is the linear endpoint weight and the real
elementary formulas. `KadiriKernelNormalForm` expands the actual kernel's
shifted sines into a common-frequency combination; its definition is not
replaced by a numerically similar surrogate.

`KadiriTransformBounds` uses the already-proved kernel nonnegativity to
bound its increasing exponential transform. For `l<=w<=r`, nonnegative
coefficients give the uniform lower bound
`a1*H(l-1)-a0*H(r) <= K(w)` and the corresponding upper bound with endpoints
reversed. This does NOT assume the signed gap itself is monotone. Both
endpoint values use the exact closed expression.

`KadiriBootstrapMaster` now exports the actual closed-form constraint and
`xi_zero_gap_of_endpoint_bootstrap_margin`. The latter connects an interval
endpoint margin to the actual divisor zero, retaining every low-height,
previous-region, and admissibility hypothesis of the original bootstrap.

The candidates were built independently before their project consumers;
the kernel identity, interval bounds, and actual bootstrap compile. All
24 audited exports use only `propext`, `Classical.choice`, and `Quot.sound`.
The 20 new regression examples and 14 existing bootstrap examples pass.
CI builds the new modules serially and runs the new regression file.

Next: substitute the existing derivative-moment bounds into the correction,
obtain uniform complete error budgets, and prove the admissible numerical
iterations starting from the established constant `56`. The improved
nonzero Gamma error and the closed `K` formula are now available; do not
reconstruct them. Finite low-height information and the final three Dusart
providers remain open, as does the exact all-`k` theorem.

### Height-decaying Gamma error (newest, 2026-09-22)

The old height-independent Gamma error has been sharpened in the actual
master and bootstrap. `DigammaEulerIdentity` factors the already-proved
finite Euler--Maclaurin identity, including both endpoints; the original
`DigammaEulerBounds` now applies its real-part majorant to that identity.
`DigammaLogBounds` exposes the common norm limit of the finite errors.
`DigammaHeightBounds` uses `norm(z+x)^2 >= (norm(z)+x)^2/2` to prove
`norm(digamma(z)-log(z)) <= 2/norm(z)` for every `Re(z)>0`.
Neither Gamma convergence nor the Euler--Maclaurin formula is reconstructed.

`SmoothedGammaNormBounds` preserves the previous real-part estimate and
adds norm- and height-decaying estimates with the same `1-kappa` leading
coefficient. `smoothedGammaFactorError` keeps `(1+kappa)/(sigma+2)` at
zero and takes the minimum with `2*(1+kappa)/abs(t)` elsewhere. The
existing `smoothedGammaFactorMajorant` uses this error, so every master
and the final bootstrap consume the improvement without a parallel chain.

`KadiriGammaBudget` now sums the individual harmonic errors in its exact
residual. Its monotonicity theorem requires `0<=kappa` as well as
`kappa<=1`, both already required by the actual master. A separate bound
extracts `2*(1+kappa)/t` times the reciprocal-weight sum over nonzero
harmonics, retaining the zero term exactly. The logarithmic coefficient
and the exact cubic-scale correction identity are unchanged in form.

The new leaves, actual bootstrap, and preserved initial master compile.
The 12 height-error examples, 14 bootstrap examples, and the earlier
Gamma and initial-region regressions pass. All 24 audited theorem closures,
including the actual bootstrap, use only `propext`, `Classical.choice`,
and `Quot.sound`. CI builds the new leaves serially before their consumers.

Next: usable uniform bounds for `K`, the derivative-moment substitution,
and admissible numerical bootstrap iterations. A sharper zero-harmonic
Gamma bound may still be useful; it has not been silently discarded.
The finite low-height inputs and three final Dusart providers remain open.

### Exact transform gap and normalized bootstrap (newest, 2026-09-22)

`KadiriTransformGap` identifies the retained transform minus the
zero-harmonic pole exactly with the paper's `K(w,theta)` integral, using
the existing positive-rescaling theorem. The actual working strip gives
`0<=w<=1`; no unjustified global monotonicity of this signed integral is used.

`KadiriBootstrapBudget` extracts the zero harmonic for arbitrary finite
sets of natural frequencies. `KadiriGammaBudget` isolates the leading
`log(t)` with coefficient sum excluding zero and proves that its explicit
residual decreases with positive base height. `KadiriBootstrapCorrection`
then rewrites the complete budget as `B*eta*log(t)+C`, preserving every
linear, quadratic, and cubic contribution, including signed linear terms.

`KadiriRegionMaster` accepts any previously established region, retaining
the separate low-height input. The old constant-56 master is now its
specialization with the same public statement. `KadiriBootstrapMaster`
derives `K<=B*eta*log(t)+C` for the actual xi divisor. A proved numerical
margin `B/Rnext<=K-C` would give the improved gap
`1/(Rnext*log(t))<=1-beta`; positivity of `B` is derived from the positive
distinguished coefficient, kernel, and `kappa<1`.

The six new leaves and preserved initial master compile. The 12 new Lean
examples and both previous initial-region and Gamma regressions pass.
All 14 new exports and the preserved initial master audit with only
`propext`, `Classical.choice`, and `Quot.sound`. CI builds the leaves
serially before certificate jobs.

That margin has NOT yet been proved for the target constants. Next:
derive usable uniform bounds for `K` and the correction, substitute the
existing four-moment bound, refine the coarse Gamma errors if needed, and
verify admissible parameter ranges for the actual iterations. Finite
low-height information and the three Dusart providers remain open. The
conditional margin theorem is not the final numerical zero-free theorem.

### Proved initial numerical region and outer separation (newest, 2026-09-22)

`ZetaZeroFreeInitial.xi_zero_gap_initial`, in namespace
`PrimeFactorUnimodality`, proves unconditionally that every actual xi zero
with `abs(Im rho)>=10^9` has
`1/(56*log(abs(Im rho))) <= 1-Re(rho)`. It optimizes the already-proved
`3,4,1` constraint at `sigma=1+1/(8*log(abs(Im rho)))`; the remaining terms
are bounded explicitly by `4*log(abs(Im rho))`. No external numerical
zero-free theorem, RH premise, or finite verification is used in this result.

`KadiriOuterSeparation` supplies the general logarithmic cutoff argument
and its specialization to the proved initial region. The actual
same-height divisor reflection gives the left side of the central strip.
The specialization retains precisely a low-height upper bound
`Re(rho)<=sigma` for zeros below `10^9`. It does not assume these zeros
lie on the critical line, although that would suffice to provide the bound.

`KadiriInitialMaster.kadiriWeight_initial_region_master_nonneg` connects
this separation to the actual explicit smoothed inequality for any finite
harmonic set. Both the former `hfar` premise and the distinguished zero's
upper strip premise are discharged. The remaining low-height input and
numerical parameter constraints are explicit.

All three new modules and seven regression examples compile. All eight
public theorem closures contain only `propext`, `Classical.choice`, and
`Quot.sound`. CI builds these leaves serially after the Gamma master.

Next: the quantitative bootstrap from the proved initial constant `56`
to the required `5.573412`, including evaluation of the retained transform,
weighted derivative mass, and the complete error budget. The paper starts
its final iterations at `5.7`; that starting constant is not yet available
here and must not be assumed. The low-height upper bound, low-zero mass,
and all three final Dusart providers remain open. Do not confuse the proved
initial region or conditional low-height assembly with the final theorem.

### Explicit smoothed Gamma terms connected to the master (newest, 2026-09-22)

`KadiriExplicitMaster.kadiriWeight_explicit_master_nonneg` replaces the
remaining Gamma terms in the actual pole/Lehman master by explicit bounds.
The declaration is in namespace `PrimeFactorUnimodality`. Its conclusion
no longer contains digamma or the smoothed Gamma boundary integral.
The outer-zero separation and numerical parameter hypotheses are retained,
not claimed as proved by this substitution.

`DigammaEulerBounds` directly applies pinned PNT Euler--Maclaurin and the
Bernoulli half-bound to reciprocal partial sums. `DigammaLogBounds` passes
to the actual digamma series limit, proving
`norm(digamma(z)-log(z)) <= 1/Re(z)` for every `Re(z)>0`. Both sides of this
estimate are necessary: `SmoothedGammaFactorBounds` preserves `1-kappa`
in the leading logarithm of the shifted difference. Its elementary height
majorant covers all signed and zero heights in `0<=Re(s)<=2`.

`SmoothedGammaBounds` sums the existing actual trivial-pole expansion,
giving `norm(remainder)<=M/4` from the second-derivative bound `M`.
`KadiriGammaRemainderBounds` supplies the actual weight's constant
`M=eta^3*(-kernel2(theta,0))`. The shifted error is at most `(1+kappa)*M/4`;
nonnegative polynomial coefficients may have any finite degree.

All six new analytic modules and the candidate facade compile. The 12 new
Lean examples and both earlier Gamma-phase and harmonic-tail regressions
pass. The 13 new theorem closures and two reused PNT inputs audit with only
`propext`, `Classical.choice`, and `Quot.sound`. CI builds the new modules
serially in `lean-foundations`, before certificates.

Next: prove the outer-zero separation for the paper's actual parameters,
evaluate the weighted derivative mass and retained real transform, and
verify the complete numerical budget giving `R=5.573412`. The finite low-zero
mass still needs its numerical lower bound. These Gamma estimates are
explicit symbolic bounds, not a verification that their constants suffice
for that numerical budget; refine them if the budget requires it.
The three Dusart providers and full all-`k` verification remain unfinished.
Do not redo the counting envelope, closed Lehman tail, pole estimates,
Gamma phase, or these smoothed Gamma bounds.

### Pole and high-tail bounds connected to the master (newest, 2026-09-22)

`kadiriWeight_lehman_pole_master_nonneg` in `KadiriLehmanMaster` now inserts both proved estimates into
the actual distinguished-zero inequality. It has no assumed counting
envelope or infinite zero-tail majorant. The separation and analytic
parameter hypotheses are unchanged and remain to be discharged.

`XiLehmanBudget` evaluates the positive-height bound into elementary
logarithms. Conjugation proves that `xiHeightTail` is even, preserving every
multiplicity label. Its combined majorant handles signed nonzero heights
and uses the existing unconditional finite low-reciprocal-mass subtraction
at zero. Every natural harmonic, including zero, is covered for any finite
polynomial once the base height is at least `10^9`. The finite low mass is
not yet replaced by a certified numerical lower bound.

`KadiriPoleBounds` reuses the existing weighted transform remainder and
the previously proved correlation positivity on the closed right half-plane.
For nonzero height the unshifted rational pole is nonpositive when
`sigma<=1`, and the entire subtracted shifted transform is nonnegative.
This gives the sharper error `eta^2*M(z,theta)/y^2`, with no shifted cubic
loss. At zero the unshifted real transform is retained exactly. The master
proves `0<=sigma-1+delta` from its existing hypotheses. Do not reconstruct
`KadiriLaplacePositivity.re_kadiriWeight_laplace_nonneg`.

All new modules build; 11 new theorems and the reused correlation-positivity
theorem audit with only `propext`, `Classical.choice`, and `Quot.sound`.
The 11-example harmonic/pole regression and the previous 13-example counting
regression pass. CI builds the new leaves serially before certificates.

Next: the separate smoothed Gamma factor/remainder estimates, outer-zero
separation, finite low-zero numerical mass, and all remaining numerical
parameters giving `R=5.573412`. Pole bounds now exist, but their numerical
budget and the final zero-harmonic transform still require evaluation.
The three final Dusart providers and full all-`k` theorem are unfinished.

### Unconditional high counting and closed Lehman tail (newest, 2026-09-22)

The numerical counting hypothesis is now discharged. `BacklundCountingHigh`
proves `|N(T)-P(T)| <= log(T)+17` at regular heights `T>=10`, then transfers
it to the actual closed xi count at every such height. Here `P` is exactly
`xiZeroCountingMainTerm`, with no `7/8` offset. The new left-limit
theorems in `XiZeroCountingEndpoints` also give the strict count's bound.
`XiLehmanHigh` obtains `|R(T)|<=2log(T)` for every `T>=10^9`, with no
zero-counting, RH, or circle-bound premise.

The proof uses the pinned PNT Euler remainder at `N=1` and the existing Euler
logarithm. On the unit circle centred at `11/10`, the surrogate has bounds
`50*abs(T)^2` everywhere and `22*abs(T)` on the right semicircle. Antipodal
averaging gives the needed logarithmic mean; using the larger bound on the
entire circle would lose the required coefficient. Two Mathlib-only
candidates, `Complex.JensenAverage` and `Integral.CircleAverageAntipodal`,
provide the general interfaces. The existing horizontal argument proof is
generalized in place; its previous Jensen export is preserved.

`xiHeightTail_le_main_add_correction_high` now bounds the actual closed tail
for `t>0`, `H>0`, `t+H>=10^9`. The exact cutoff multiplicity combines with
the closed count to give the strict boundary count, whose left-limit bound
removes the previously uncontrolled atom. No assumption that the cutoff
avoids zeros is needed. The regression covers every natural harmonic
`k>=1` at `t=k*30600000000`, `H=100000`.

The new leaves and full candidate facade compile. All 32 new theorem
closures, plus the preserved Jensen export, contain only `propext`,
`Classical.choice`, and `Quot.sound`. The 13 new Lean examples and four
earlier analytic regression files pass. Fast checks pass; CI builds these
leaves serially in `lean-foundations`, without replaying certificates.

Next: substitute the proved high tail into the actual weighted master,
handle its zero harmonic using the existing low-reciprocal-mass bound,
and prove the remaining separation and smoothed pole/gamma estimates.
The numerical parameters giving `R=5.573412`, all three final Dusart
providers, and full all-`k` verification remain unfinished. Do not redo
the now-proved counting envelope or confuse the counting Gamma phase bound
with the separate smoothed Gamma error estimates.

### Uniform Gamma phase and discharged counting contour (newest, 2026-09-22)

`GammaLogBranch` reuses PNT's actual `Complex.logGammaSeq`, its Cauchy
convergence, and its digamma series. It exports the canonical limit's
derivative and exponential identity; positive real inputs have imaginary
part zero. The local uniform-derivative proof is adapted from the interior
of Robby Sneiderman's `hasSum_digamma_of_re_pos`, with attribution and the
same pinned revision. No Gamma branch or phase identity is assumed.

The Mathlib-only `IntervalIntegral.Trapezoid` candidate proves the exact
second-derivative integral remainder. `Complex.LogTrapezoid` specializes it
to horizontal logarithms, sums the reciprocal bounds, and proves the finite
sum identity. `Complex.LogShiftLimit` uses Mathlib's existing scaled-log
limit to remove the far endpoint. These give the actual theorem
`abs_gammaRightLog_im_sub_stirling_le`: the phase differs from
`Im ((z-1/2)*log z-z)` by at most `1/(8*Re z)` for every `Re z>0`.
The bound is uniform in imaginary height, not an integrated `O(T)` error.

`XiGammaContour` connects that branch to the actual separated integrand,
cancels the corner exactly, and obtains error at most `1/10` at
`z=5/4+iT/2`. Both contour identities cover zero and negative heights.
For `T>0`, the difference from `T/2*log(T/(2*pi))-T/2` is bounded by
`3*pi/8+27/20`.

`BacklundCountingMainTerm.abs_zeta_N_sub_mainTerm_le_circle` now bounds
the actual `|N(T)-xiZeroCountingMainTerm T|` by
`7/8+27/(20*pi)+log(1/(sigma-1)+1)/pi`
plus `log(M*(1/(sigma-1)+1)/T)/log(R/r)`.
Only the explicit circle bounds and regular-height hypotheses remain in
this estimate. The existing regular-height transfer handles closed cutoff
multiplicities; the numerical circle bound and constants must still be
proved before claiming `2log(T)`.

All seven new proof leaves and the candidate facade compile. The 26 new
theorem axiom closures contain only `propext`, `Classical.choice`, and
`Quot.sound`. The new 13-example `GammaCountingPhase` regression and the
previous vertical-argument regression pass. CI builds the new leaves
serially in `lean-foundations`, before certificate jobs. The candidate
facades and inventory are updated. No certificate replay was run.

Next: prove the explicit circle magnitude estimate, choose and verify the
parameters for the required counting envelope, and apply the already-proved
regular-height/closed-count transfer. Gamma and vertical-argument bounds
are now proved inputs, not hypotheses to reconstruct. The numerical
zero-free parameters, separation input, three final Dusart providers, and
the full all-`k` verification remain unfinished.

### Vertical argument and explicit Jensen centre (newest, 2026-09-22)

The vertical surrogate integral and centre lower bound are now proved.

- The Mathlib-only `LSeries.RiemannZetaEulerLog` candidate represents an
  analytic logarithm by the Dirichlet series with coefficients `Lambda/log`.
  It directly reuses Mathlib's Euler-product exponential identity and
  L-series differentiation. Nonnegative coefficients give the sharp bound
  `norm(EulerLog(s)) <= log(norm(zeta(Re(s))))`; the logarithm is real on
  the real axis. This also gives the lower bound
  `1/norm(zeta(Re(s))) <= norm(zeta(s))`.
- `BacklundVerticalArgument` adds `log(s-1)` to this Euler logarithm,
  differentiates to the actual surrogate logarithmic derivative, and
  integrates it exactly. The vertical imaginary part is bounded by
  `pi/2 + log(norm(zeta(sigma)))` for every real height, including negative
  and zero heights. There is no uncontrolled principal-log branch change.
- The same module proves the centre bound
  `abs(T)/norm(zeta(sigma)) <= norm(a(sigma+i*T))`.
- `BacklundCountingEstimate` inserts both estimates into the proved
  actual counting contour and Jensen inequality. Finally the existing
  real-axis Abel bound replaces `norm(zeta(sigma))` by
  `1/(sigma-1)+1`. Only the gamma contribution and circle magnitude bounds
  remain unestimated in this counting inequality; the circle and
  regular-height hypotheses are explicit, not presumed discharged.

The candidate, its facade, and both project leaves compile. All 21 public
theorems have only `propext`, `Classical.choice`, and `Quot.sound` in their
axiom closures. The new 12-example Lean regression and the preceding
counting-decomposition regression pass. CI builds candidate then consumers
serially before certificates. The root candidate facade retains 12 imports.
Fast checks, Ruff format/lint, mypy, actionlint, and 106 Python tests pass.

NEXT: sharp integrated gamma/Stirling and explicit circle magnitude bounds
sufficient for the actual `2log(T)` error at the required cutoff. Do not
repeat the vertical argument or introduce a counting-error assumption as a
replacement. Separation, numerical zero-free parameters, and all three
final Dusart providers remain open.

### Actual counting contour and half-contour identity (newest, 2026-09-22)

The argument-principle identity for the actual multiplicity-weighted count
is now proved, rather than supplied as a hypothesis.

- `ZetaXiRealNonvanishing` applies the pinned Abel continuation to prove
  zeta's strict negativity for `1/2<=sigma<1`, then uses the gamma product
  and xi reflection to exclude every real xi zero. The Abel domain is only
  used where its actual `Re(s)>1/10` hypothesis holds.
- `XiCountingRectangle` identifies the xi divisor support on the rectangle
  with vertical sides `1-sigma,sigma` and heights `0,T` with PNT's strict
  positive-height zeta zero set. Existing multiplicity equality supplies its
  weights. The audited PNT rectangle residue theorem gives exactly
  `RectangleIntegral'(logDeriv xi)=N(T)` when `sigma>=1,T>=0` and the top
  avoids zeros. No separate argument-count identity is assumed.
- `XiHalfContour` uses global logarithmic-derivative conjugation and the
  existing reflection identity to prove
  `pi*N(T)=Im(VIntegral(logDeriv xi,sigma,0,T))-Im(HIntegral(logDeriv xi,1/2,sigma,T))`.
  It proves the necessary top-line continuity and preserves contour signs.
- `XiRegularHeights` proves that all heights sufficiently close above any
  nonnegative cutoff avoid xi zeros. Continuous count-error bounds established
  at such regular heights transfer to the closed count at every cutoff,
  including the full multiplicity at a zero ordinate.
- `ZetaXiLogDerivative` now exposes its existing product differentiation on
  `Re(s)>0` away from one and at zeta nonzeros. The former `Re(s)>1` theorem
  is retained as a wrapper with exactly its previous statement.
  `BacklundXiLogDerivative` separates the xi integrand into the entire
  surrogate integrand, `-log(pi)/2`, and `digamma(s/2+1)/2`. This makes the
  preceding horizontal Backlund bound applicable inside the critical strip.
- `XiCountingDecomposition` proves integrability and splits both actual
  half-contour integrals into surrogate and gamma terms. The horizontal
  Jensen theorem now bounds the actual count minus the gamma contribution,
  leaving the vertical surrogate integral and explicit circle bounds visible.
  Its gamma continuity comes directly from PNT's proved `DigammaSeries`.

All six new leaves and the generalized logarithmic-derivative module compile.
The 31 new theorems and two retained exports have only `propext`,
`Classical.choice`, and `Quot.sound` in their audited closures. Both new Lean
regressions pass (17 examples), as do the existing counting-bridge and
horizontal-argument regressions. CI builds these modules serially before
certificates. Fast checks, Ruff, mypy, actionlint, and 105 Python tests pass.

NEXT: prove sufficiently sharp explicit gamma/Stirling, vertical surrogate,
and circle-to-centre surrogate estimates. The existing `DigammaExplicitBounds`
upper bound has
an additive constant; integrating it directly gives an error proportional
to `T`, not the required logarithmic discrepancy. A sharper integrated
gamma remainder is needed. The numerical `2log(T)` count bound, separation,
numerical zero-free parameters, and all three Dusart providers remain open.
Do not repeat the completed contour, integral splitting, or regular-height arguments.

### Horizontal argument integral bound (newest, 2026-09-22)

The real-crossing comparison and infinite-power limit are now proved and
connected to the actual horizontal logarithmic-derivative integral.

- `Trigonometric.ZeroCount` bounds the absolute endpoint change of a
  continuous phase by `(number of cosine zeros + 1)*pi`. The proof counts
  integer-spaced levels and uses the intermediate value theorem; it allows
  decreasing and nonmonotone phases. It does not assert bounded total variation.
- `Complex.Log.Interval` uses Mathlib's exponential covering and path lifting
  to construct a continuous logarithm on a nonvanishing closed segment with
  prescribed initial value. It includes degenerate segments and never assumes
  the principal argument is continuous along the path.
- `BacklundArgument` applies the phase lemma to each positive power and uses
  the unbounded good powers from recurrence. The limit removes the `1/n`
  endpoint allowance and the `log(2)/n` centre loss. Its bound is exactly
  `pi*log(M/abs(a(sigma+iT)))/log(R/r)` under the stated circle bounds.
- `Complex.Log.IntervalIntegral` derives the derivative of a continuous
  logarithm by the existing inverse-derivative theorem, then applies FTC.
  `BacklundArgumentIntegral` proves integrability and the exact integral
  increment for the entire surrogate and transfers the Jensen bound to the
  imaginary part of its horizontal logarithmic-derivative integral.

All three candidates and both project leaves compile. The 13 public results
use only `propext`, `Classical.choice`, and `Quot.sound`. The eight-example
`BacklundArgument` regression and the previous auxiliary regression pass;
CI builds each leaf serially before certificates. Ruff, mypy, actionlint,
and all 103 Python tests pass.

NEXT: the actual count's argument-principle identity, followed by sufficiently
explicit gamma/Stirling and circle-to-centre magnitude bounds. The horizontal
comparison no longer needs a new phase or integral bridge. The existing PNT
`RectangleArgumentPrinciple.rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`
(a root-level declaration despite the module path) is a promising reusable
residue theorem; audit its closure before using it. Its companion
`rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt` assumes an argument
integral identity, so it alone does not discharge that identity.
The numerical `2log(T)` estimate, separation, numerical parameters, and all
three final Dusart providers remain open.

### Backlund auxiliary and Jensen crossing bound (newest, 2026-09-22)

The actual auxiliary function from Trudgian's equation (2.4) is now entire,
and its real zeros satisfy Jensen's bound at arbitrarily large powers.

- `BacklundAuxiliary` directly reuses PNT's residue-patched entire surrogate
  `a(s)=(s-1)zeta(s)` and its differentiability proof. It proves conjugation,
  the real-axis identity, and norm bounds for the symmetrized powers.
- `Complex.Powers.Recurrence` proves recurrence of unit complex powers by
  compactness, including torsion points. It supplies unbounded powers with
  real part at least half the norm power, hence a nonzero auxiliary centre.
- `BacklundJensen` applies Mathlib's proved `sum_divisor_le` to obtain the
  explicit disk-divisor bound in terms of the boundary magnitude and centre.
- `Complex.JensenCard` proves that distinct zeros contribute at least their
  cardinality to the analytic divisor on a compact connected domain.
  `BacklundRealZeros` applies this to the actual horizontal real-part zeros,
  proves their finiteness, and transfers the explicit Jensen estimate.

Both candidates, all three project leaves, and the Lean regression compile.
The 21 new public theorems and PNT's surrogate differentiability use only
`propext`, `Classical.choice`, and `Quot.sound`. Fast checks, 102 Python tests,
Ruff, mypy, and actionlint pass. CI builds these leaves serially before
certificates. No certificate replay is needed for this increment.

NEXT: prove the argument-variation bound from real crossings, the argument
principle identity for the actual count, and adequate explicit gamma/Stirling
and boundary magnitude estimates. The current Jensen theorem retains its
boundary norm hypotheses; it does not yet prove the required `2log(T)` bound.
The remaining separation and numerical inputs and three Dusart providers
are still open. Do not repeat the completed counting and integral bridges.

### Exact xi/zeta counting bridge (newest, 2026-09-22)

The counting-convention bridge is now proved, including analytic multiplicity
and every upper-cutoff zero. It introduces no RH premise.

- `XiZeroCountingEndpoints` defines the strict xi count and proves that
  the closed count is the strict count plus the full ordinate multiplicity
  at positive cutoffs. Local finiteness proves that strict counts tend to
  the closed count from the right. Continuous error envelopes therefore
  transfer at zero heights without discarding the endpoint atom.
- `ZetaXiMultiplicity` proves equality of the xi and zeta analytic orders
  on the right half-plane away from one, hence equality of xi's integer
  divisor with PNT's `riemannZeta.order`. It also places xi zeros in the
  open critical strip and sends every nonreal zeta zero to an xi zero.
- `XiZetaCountingBridge` groups finite xi labels by complex value using
  PNT's already-proved divisor-fiber cardinality. It proves, for all real
  `T`, `(xiStrictZeroCount T : Real)=riemannZeta.N T`. For `T>0`, the closed
  count is `N(T)+m(T)`. This uses only PNT's definitions and divisor API,
  not its much larger `KadiriZeroCounting` import or an assumed count bound.
- `XiZetaCountingBounds` transfers any stated Riemann-von Mangoldt bound
  to the closed count, with the exact `7/8` offset. Its elementary comparison
  shows that constants `0.137,0.443,6.1` imply the needed `2log(T)` envelope
  when `T>=2` and `log(T)>=5`. The resulting actual Lehman tail estimate
  still requires that RvM hypothesis and retains the boundary atom.

All four leaves and `test/lean/XiZetaCountingBridge.lean` compile. The 21
audited exports use only `propext`, `Classical.choice`, and `Quot.sound`.
CI builds the leaves serially before certificate work; the Python ordering
regression is included. No sharp count theorem has been imported as proved.

NEXT: the actual quantitative counting theorem, not another counting bridge.
One may prove the required `2log(T)` estimate directly at the relevant high
cutoff; proving the stronger conventional constants is not obligatory.
The source route is the argument-principle identity, explicit gamma/Stirling
error, and a Jensen bound for the horizontal argument variation; see
[Trudgian, sections 2--3](https://arxiv.org/pdf/1208.5846).
The integral reduction, multiplicity match, cutoff transfer, and offset
conversion are now complete. Separation, pole/gamma bounds, numerical
inputs, and all three final Dusart providers remain open.

### Exact infinite discrepancy and conditional Lehman estimate (newest, 2026-09-22)

The smooth main term has now been subtracted from the unconditional infinite
counting identity. This completes that analytic reduction, not the explicit
zero-counting theorem needed to apply its quantitative bound.

- `MeasureTheory.Integral.IoiTranslation` proves translation of half-line
  integrability and integrals, including vector-valued integrands.
- `Integrals.ReciprocalSquarePairWeighted` proves the necessary weighted
  integrability and vanishing boundaries, allowing signed logarithmic
  factors. It also proves
  `integral_A^infinity log(x)*w_t(x) dx = log(A)*phi_t(A)+integral_A^infinity phi_t(x)/x dx`.
- `XiLehmanSmoothTerm` proves integrability of `P*w_t`, the vanishing
  boundary `P(T)*phi_t(T)`, and its exact main-integral identity.
- `XiLehmanRemainder` proves genuine integrability of `R*w_t` and the
  unconditional identity
  `sum_(gamma>A) phi_t(gamma)-Main = -R(A)*phi_t(A)+integral_A^infinity R(x)*w_t(x) dx`.
  Its quantitative theorem assumes the actual bound `|R(x)|<=2log(x)` for
  every `x>=A`. Under that hypothesis it derives the existing Lehman
  correction. The closed tail retains exactly `m(A)*phi_t(A)`.

All four new leaves compile. The 21 audited exports use only `propext`,
`Classical.choice`, and `Quot.sound`. The regression
`test/lean/XiLehmanRemainder.lean` checks signed weights, complex translation,
the unconditional identity, and the explicit hypotheses of the estimate.
CI builds the new leaves serially before certificate jobs.

NEXT: prove the actual explicit counting discrepancy bound and the remaining
separation, pole/gamma, and numerical inputs. The three final Dusart providers
remain open. Do not repeat the now-completed improper-integral reduction.
If reusing PNT counting machinery, its pinned `riemannZeta.N` counts
`0<gamma<T`, whereas `xiZeroCount` counts `0<gamma<=T`. They cannot simply be
equated at a zero height: account for the endpoint multiplicity or prove a
right-limit transfer using local finiteness. Its Riemann-von Mangoldt main
term also includes `7/8`, while this project's `P` does not.

### Unconditional infinite counting integral (newest, 2026-09-22)

The finite-to-infinite passage is now proved for the actual reciprocal-square
xi tail. It does not need a sharp zero-counting estimate: the previously
proved summability and monotonicity suffice to kill the upper boundary.

- `InfiniteSum.Sublevel` reuses Mathlib's cofinal finite-sum limit and
  dominated convergence for series. It proves sublevel exhaustion and
  `card{sublevel T}*f(T) -> 0` for nonnegative decreasing weights tending
  to zero whose values at the indexed locations are summable. Repeated
  locations retain separate indices.
- `XiZeroCountingLimits` applies those results to actual strict-positive
  xi tails. In particular, `N(T)*f(T) -> 0` follows after adding the finite
  low-count contribution. No Backlund constant is assumed for this limit.
- `XiZeroCountingImproper` proves absolute integrability of `N(x)*f'(x)`
  from the finite Abel identity, summability, the vanishing upper boundary,
  and `f'<=0`. The norm integrals converge, so this is not an identity
  involving an unverified improper integral.
- `Integrals.ReciprocalSquarePairDeriv` supplies the pair's explicit
  derivative and its zero limit at infinity. `XiLehmanAbel` discharges all
  the preceding hypotheses for `t>=0,H>0`. With `A=t+H`,
  `phi_t(x)=1/(x-t)^2+1/(x+t)^2`, and `w_t=-phi_t'`, it proves
  `sum_(gamma>A) phi_t(gamma) = integral_A^infinity N(x)*w_t(x) dx-N(A)*phi_t(A)`.
  The closed `xiHeightTail` adds exactly `m(A)*phi_t(A)`.

Both candidate leaves and all three project leaves compile. The 12 theorem
exports in `.research/DusartInfiniteCountingAxioms.lean` use only `propext`,
`Classical.choice`, and `Quot.sound`. The CI serial build and regression
`test/lean/XiZeroCountingTail.lean` check exhaustion at repeated heights,
the zero-height counting boundary, integrability, and the cutoff atom.

NEXT: subtract the smooth main term from this unconditional infinite
identity, using the exact main integral already proved. Prove the actual
explicit counting discrepancy bound, rather than substituting the crude
existential count or an RH hypothesis. A bridge to the sibling zeta-order
count may help that quantitative proof, but is no longer needed merely to
justify convergence or the upper-boundary limit. Separation, pole/gamma
estimates, numerical inputs, and the three final Dusart providers remain
open. Do not repeat the completed finite/infinite Abel work.

### Exact logarithmic integral and finite xi counting identity (newest, 2026-09-22)

The main Lehman integral now has a proved closed form. The finite
counting-to-integral step is also implemented for the actual xi divisor,
with multiplicity and both boundary terms. These results do not prove the
remaining numerical zero-counting bound.

- `Integrals.LogReciprocalSquarePair` proves genuine improper integrability
  for every positive `t,H,a`, including sign changes near the lower cutoff,
  and the exact identity
  `integral_H^infinity log((x+t)/a)*phi_t(x+t) dx =
  log((H+t)/a)*(1/H+1/(H+2t))+log((H+2t)/H)/t`.
  The primitive and its limit at infinity are proved, not assumed.
- `XiLehmanMainIntegral` specializes `a=2π`, supplies the actual main
  integral's integrability, and combines its exact value with the previously
  proved elementary correction. This expression needs no numerical quadrature.
- The Mathlib-only `MeasureTheory.Integral.FinsetAbel` proves weighted
  summation by parts for arbitrary real locations. Different labels may
  have the same location, and weights need not be nonnegative. Its proof
  integrates finite indicator functions and uses Mathlib's FTC.
- `XiZeroCountingAbel` defines `xiZeroCount(T)` by the finite set of actual
  divisor labels with `0<gamma<=T`. Its half-open window `(a,b]` counts
  `N(b)-N(a)`, and its exact Abel identity is
  `sum_(a<gamma<=b) f(gamma) = N(b)f(b)-N(a)f(a)-integral_a^b N(x)g(x) dx`
  for `f'=g` and integrable `g`.
- `XiZeroCountingRemainder` defines
  `P(T)=T/(2π)*log(T/(2π))-T/(2π)` and the actual error `R(T)=N(T)-P(T)`.
  It proves `P'=log(T/(2π))/(2π)` and the exact finite identity
  `sum f(gamma)-integral P'(x)f(x) dx =
  R(b)f(b)-R(a)f(a)-integral R(x)g(x) dx`.
  The absence of a `7/8` constant is deliberate; any external counting
  estimate using that offset must be converted explicitly.

The two candidate leaves and three project leaves compile. The 25 exported
theorems audited in `.research/DusartCountingIntegralAxioms.lean` use only
`propext`, `Classical.choice`, and `Quot.sound`. Lean regressions cover repeated
heights, signed weights, lower/upper endpoints, the empty window, and the
constant-function discrepancy signs. CI builds the new leaves serially and
runs both `test/lean/XiHeightTail.lean` and `test/lean/XiZeroCounting.lean`.

NEXT: pass the finite counting-error identity to the infinite tail and
prove the explicit bound for the actual `R(T)`. The sibling PNT's crude
unconditional count suffices for convergence, not the required numerical
error; its sharper Riemann-von Mangoldt route retains that bound as a
hypothesis. Relate its zeta-order count to the xi divisor count if using its
proved lower-level counting machinery. Preserve the closed-cutoff atom
from `XiHeightTailEndpoint`. Absolute-height separation, pole/gamma bounds,
actual numerical inputs, and all three final Dusart providers remain open.
Do not redo the exact integral or finite Abel proofs. Non-certificate work
continues to take priority over replays.

### Positive tail, endpoint correction, and unconditional low-mass subtraction (newest, 2026-09-22)

The actual height tail now has its positive-ordinate decomposition, its
closed-cutoff correction, and a new unconditional finite-mass bound at
height zero. The elementary integral in the positive-height Lehman error
is also proved. The zero-counting theorem underlying Lehman's estimate is
NOT supplied by these steps.

- `XiHeightTailPairing` uses the existing actual divisor conjugation
  equivalence. Every multiplicity label is preserved. It proves absolute
  convergence and
  `Σ(t,H)=sum_{γ>=|t|+H} [1/(γ-t)²+1/(γ+t)²]`, including the cutoff.
- `XiLowReciprocalMass` proves finiteness of bounded-ordinate divisor
  sets, defines the actual finite sum `L(H)=sum_{|γ|<H} Re(1/ρ)`, and proves
  the exact closed-tail reciprocal mass is
  `(2+EulerConstant-log(4π))/2-L(H)`. This reuses the already-proved
  unconditional real Hadamard constant, not an RH-dependent mass identity.
- The Mathlib-only `Poisson.Reciprocal` controls `1/γ²` by the reflected
  reciprocal pair with factor `1+1/H²` on the whole closed critical strip.
  `XiHeightTailZero.xiHeightTail_zero_le_reciprocal_mass` consequently proves
  `Σ(0,H) <= 2(1+1/H²)*[(2+EulerConstant-log(4π))/2-L(H)]` for every `H>0`.
  Its finite-subset corollary needs only a verified lower sum over distinct
  actual divisor labels below `H`, not an exhaustive enumeration of all
  low zeros. No such numerical zero certificates are claimed implemented.
  This is an alternative to the paper's separate `0.023105` inverse-height
  total bound; whether a chosen finite input meets the final numerical
  budget must still be checked.
- `XiHeightTailEndpoint` proves that each ordinate fiber is finite and
  `Σ(t,H)=sum_{γ>|t|+H} φ_t(γ)+m(|t|+H)*φ_t(|t|+H)`, where `m` counts all
  divisor labels on the boundary and `φ_t(x)=1/(x-t)²+1/(x+t)²`.
  A strict-tail bound therefore transfers only with this atom correction
  or a proved zero boundary multiplicity. No endpoints are silently lost.
- `Integrals.ReciprocalSquarePair` proves positivity, continuity,
  antitonicity, actual improper integrability, and
  `integral_H^infinity φ_t(x+t)/(x+t) dx <= 2/(tH)` for `t,H>0`.
  `XiLehmanIntegral` obtains the exact elementary correction
  `4 log(t+H) [1/H²+1/(H+2t)²]+4/(tH)`. It does not assert that a zero
  sum already satisfies the unproved Lehman counting estimate.

The two candidates and five project leaves compile. The 29 audited theorem
exports use only `propext`, `Classical.choice`, and `Quot.sound`.
The regression `test/lean/XiHeightTail.lean` checks label preservation,
cutoff atoms, the strict finite subtraction, the empty finite-subset case,
the inverse-square integral, and the divided-pair correction. CI builds
the new chain serially in `lean-foundations` before running it.

NEXT: prove the zero-counting/integration argument for the positive-height
Lehman estimate, the source's absolute-height separation, and the remaining
pole/gamma estimates. A useful analytic simplification for the main Lehman
integral is recorded privately for proof next; it is not yet a theorem.
Then prove the actual numerical low-zero/moment/parameter inputs and all
three final Dusart providers. Do not repeat the completed conjugation,
pairing, summability, rational comparison, or low-mass algebra. Non-certificate
work remains and continues to take priority over finite replay.

### Outer height-tail master (2026-09-22)

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

The newer section supplies positive-height reindexing, cutoff correction,
and an unconditional alternative to the height-zero inverse-square total
bound. Absolute-height separation and the quantitative positive-height
counting estimate remain. Pole/gamma bounds, the exact parameter and moment
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
