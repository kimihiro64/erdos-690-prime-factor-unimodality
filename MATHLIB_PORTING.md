# Mathlib candidate layer

Reusable mathematics intended for possible upstreaming lives under
`PrimeFactorUnimodality/Mathlib/` and is exported by `PrimeFactorUnimodality/Mathlib.lean`.
The child generator replaces `PrimeFactorUnimodality` with the configured project
namespace.

## Hard boundary

A Mathlib candidate module may import only:

- narrow `Mathlib.*`, `Batteries.*`, `Init.*`, `Lean.*`, or `Std.*` modules;
- another module inside the same `<Project>.Mathlib` candidate layer.

It may not import project definitions, helpers, proof branches, assembly,
`Challenge`, `Solution`, or a third-party project library. Its declarations
must use the namespace they would have after upstreaming, never the project's
namespace. The architecture audit enforces these dependency and namespace
rules.

## File and declaration standards

Each real candidate file should:

1. mirror its proposed Mathlib destination after the `<Project>/Mathlib/`
   prefix is removed;
2. use Mathlib's copyright, Apache-2.0 licence, author, module-documentation,
   declaration-documentation, naming, and formatting conventions;
3. state results at reusable generality without headline-theorem terminology;
4. use narrow, sorted, nonredundant imports and avoid project-only dependencies;
5. build independently before the project modules that consume it;
6. include focused regression examples or tests when behavior is not captured
   by a theorem statement alone;
7. contain no `sorry`, local axioms, discovery commands, or generated proof
   shortcuts.

## Candidate inventory

Replace the scaffold row when the first real candidate module is created.

| Project module | Proposed Mathlib path | Readiness | Upstream reference |
| --- | --- | --- | --- |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.Chebyshev.PsiBounds` | `Mathlib/NumberTheory/Chebyshev/PsiBounds.lean` | project-verified | Linear psi bounds from the decreasing elementary logarithmic error; a rational square and endpoint logarithm control a full ray. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSievePeriodic` | `Mathlib/NumberTheory/PartialSievePeriodic.lean` | project-verified | Exact wheel-period lookup from proved remainder counts and totient; reuses the periodic Nat.count candidate and Mathlib's interval totient identity. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSieve` | `Mathlib/NumberTheory/PartialSieve.lean` | project-verified | Exact coprime-interval counts, prime removal, executable list/indexed recurrence, and prefix congruence; Mathlib-only proof. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSievePrimeLeaves` | `Mathlib/NumberTheory/PartialSievePrimeLeaves.lean` | project-verified | Complete primorial sieve stopping rule with strict square boundary; actual prime counts from checked recurrence values. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.PrimeCountingMeissel` | `Mathlib/NumberTheory/PrimeCountingMeissel.lean` | project-verified | Complete canonical prime prefix and exact Meissel identity by telescoping removal; explicit cube/square cutoff guards. |
| `PrimeFactorUnimodality.Mathlib.Data` | `Mathlib/Data.lean` | project-verified | Facade for finite-data candidates within the import limit. |
| `PrimeFactorUnimodality.Mathlib.Data.Nat.BitCount` | `Mathlib/Data/Nat/BitCount.lean` | project-verified | Balanced bitset counting, exact clipped/offset block semantics, and adjacent-block composition. |
| `PrimeFactorUnimodality.Mathlib.Data.Nat.BitCountPacked` | `Mathlib/Data/Nat/BitCountPacked.lean` | project-verified | Carry-free whole-integer lane merging, proved equal to the original bit count for every depth; exact block cardinality and adjacent-block composition. |
| `PrimeFactorUnimodality.Mathlib.Data.Nat.BitLaneCompare` | `Mathlib/Data/Nat/BitLaneCompare.lean` | project-verified | Packed strict unsigned comparisons with checked lane bounds and proved absence of inter-lane borrow or carry. |
| `PrimeFactorUnimodality.Mathlib.Data.Nat.BitProduct` | `Mathlib/Data/Nat/BitProduct.lean` | project-verified | Balanced bit-selected products in any commutative monoid, exact offset/clipping semantics and adjacent-block composition. |
| `PrimeFactorUnimodality.Mathlib.Algebra` | `Mathlib/Algebra.lean` | project-verified | Facade for algebraic candidates within the direct-import limit. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier` | `Mathlib/Analysis/Fourier.lean` | project-verified | Facade for shared transforms and rational checking, within the direct-import limit. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RationalAlias` | `Mathlib/Analysis/Fourier/RationalAlias.lean` | project-verified | Exact sparse rational coordinate assembly and equality with the existing complex alias input. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RationalTrace` | `Mathlib/Analysis/Fourier/RationalTrace.lean` | project-verified | Executable rational trace checks, one shared twiddle table per depth, full semantic soundness and an exact rational recursive error budget. |
| `PrimeFactorUnimodality.Mathlib.Algebra.BigOperators.Ring.Horner` | `Mathlib/Algebra/BigOperators/Ring/Horner.lean` | project-verified | List Horner folds equal finite power sums on arbitrary coefficient slices over any semiring. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.RationalPoint` | `Mathlib/Analysis/Complex/RationalPoint.lean` | project-verified | Exact Gaussian rational arithmetic and a complete Boolean squared-norm comparison. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixRoot` | `Mathlib/Analysis/Fourier/RadixRoot.lean` | project-verified | Shared canonical roots, bounded twiddle phases and exact parent/child compatibility. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier.GroupedGrid` | `Mathlib/Analysis/Fourier/GroupedGrid.lean` | project-verified | Sparse alias-array identity and complete shared-trace errors for moment polynomials on signed grids. |
| `PrimeFactorUnimodality.Mathlib.Data.Vector.ScatterAdd` | `Mathlib/Data/Vector/ScatterAdd.lean` | project-verified | Sparse shared-array accumulation, repeated-index sums and append composition. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixError` | `Mathlib/Analysis/Fourier/RadixError.lean` | project-verified | Shared recursive trace validity and complete input, twiddle and arithmetic error assembly, with error nonnegativity from validity. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier.IntegerGrid` | `Mathlib/Analysis/Fourier/IntegerGrid.lean` | project-verified | Exact link to Mathlib DFT, signed integer grid phases and complete modulo-grid coefficient aliasing. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixTwo` | `Mathlib/Analysis/Fourier/RadixTwo.lean` | project-verified | Materialized radix-two transform, successive twiddle powers, complete finite-sum identity and butterfly-output count. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.GroupedEvaluation` | `Mathlib/NumberTheory/LSeries/GroupedEvaluation.lean` | project-verified | Exact cpow height-shift factorization and complete grouped/rounded finite Dirichlet-sum errors. |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedRounding` | `Mathlib/Analysis/SpecialFunctions/Complex/GroupedRounding.lean` | project-verified | Independent complex phase and shared-moment errors, including the complete Taylor remainder. |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedExponential` | `Mathlib/Analysis/SpecialFunctions/Complex/GroupedExponential.lean` | project-verified | Finset fiber sums, shared Taylor moments and nearest-integer residual bounds. |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialStability` | `Mathlib/Analysis/SpecialFunctions/Complex/ExponentialStability.lean` | project-verified | Complete coefficient/frequency perturbation budgets and finite first-moment interpolation, retaining repeated frequencies. |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialMoments` | `Mathlib/Analysis/SpecialFunctions/Complex/ExponentialMoments.lean` | project-verified | Reuses Mathlib exponential remainder, finite-sum interchange and norm comparison; a successive-atom recurrence shares powers and factorial quotients across moment orders. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ExplicitBound` | `Mathlib/NumberTheory/BernoulliPeriodic/ExplicitBound.lean` | project-verified | Explicit rational coefficient-sum majorant replaces the existential compactness bound for complete power tails; an exact finite Bernoulli-number formula makes the budget executable. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory` | `Mathlib/NumberTheory.lean` | project-verified | Facade for number-theoretic candidates |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.Chebyshev.Intervals` | `Mathlib/NumberTheory/Chebyshev/Intervals.lean` | project-verified | Exact prime-set differences and complete theta-increment enclosures from prime-count differences and endpoint logarithms; uses pinned Mathlib finite-sum and prime-set lemmas. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic` | `Mathlib/NumberTheory/BernoulliPeriodic.lean` | project-verified | Facade for complete periodic Bernoulli power tails |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Normalized` | `Mathlib/NumberTheory/BernoulliPeriodic/Normalized.lean` | project-verified | WIPResearch `bdc46941c4f2e13fb84e0a338b905bb10e711357`, Jonas Whidden, Apache-2.0: normalized polynomial derivatives and unit-cell integration by parts; original `Polynomial` names retained. The rational endpoint evaluation additionally connects numerical Bernoulli coefficients. |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Integrability` | `Mathlib/NumberTheory/BernoulliPeriodic/Integrability.lean` | project-verified | Same WIP leaf: measurable periodic profiles and absolute improper-tail integrability |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Cells` | `Mathlib/NumberTheory/BernoulliPeriodic/Cells.lean` | project-verified | Same WIP leaf: almost-everywhere integer-cell translation and finite telescoping |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Recursion` | `Mathlib/NumberTheory/BernoulliPeriodic/Recursion.lean` | project-verified | Same WIP leaf: exact infinite-tail recursion with boundary terms retained |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.RotationError` | `Mathlib/Analysis/SpecialFunctions/Complex/RotationError.lean` | project-verified | Exact polar rescaling, rotation/reciprocal error, integer quarter-turn reduction and sign preservation for a real rotated value under a phase perturbation smaller than a quarter turn. |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex` | `Mathlib/Analysis/SpecialFunctions/Complex.lean` | project-verified | Narrow facade for logarithmic height bounds, shifted limits and trapezoid errors |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogHeightBounds` | `Mathlib/Analysis/SpecialFunctions/Complex/LogHeightBounds.lean` | project-verified | Height-decaying squared-norm logarithmic correction and both upper-quadrant argument deviations from elementary tangent bounds |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogContinuity` | `Mathlib/NumberTheory/LSeries/RiemannZetaLogContinuity.lean` | project-verified | Continuity of finite horizontal zeta logarithmic integrals at every positive height, including zero ordinates |
| `PrimeFactorUnimodality.Mathlib.Analysis.Meromorphic.HorizontalFactorization` | `Mathlib/Analysis/Meromorphic/HorizontalFactorization.lean` | project-verified | Compact meromorphic factorization gives exact horizontal logarithmic integral decomposition, including singular heights |
| `PrimeFactorUnimodality.Mathlib.Analysis.Meromorphic.HorizontalContinuity` | `Mathlib/Analysis/Meromorphic/HorizontalContinuity.lean` | project-verified | Continuity through zeros and poles from finite logarithmic singularities and a clipped continuous remainder |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.HorizontalContinuity` | `Mathlib/Analysis/Complex/Log/HorizontalContinuity.lean` | project-verified | Continuity of horizontal logarithmic-distance integrals through zero heights, using a uniform integrable logarithmic singularity |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.FiniteExceptions` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FiniteExceptions.lean` | project-verified | FTC for continuous real primitives with integrable derivatives away from finitely many exceptional points |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogTailDerivative` | `Mathlib/NumberTheory/LSeries/RiemannZetaLogTailDerivative.lean` | project-verified | Differentiation of the entire horizontal logarithmic tail by dominated convergence and exact endpoint Euler argument |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerIntegral` | `Mathlib/NumberTheory/LSeries/RiemannZetaEulerIntegral.lean` | project-verified | Vanishing Euler logarithm at horizontal infinity and exact complete logarithmic-derivative integral by improper FTC |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogDerivDecay` | `Mathlib/NumberTheory/LSeries/RiemannZetaLogDerivDecay.lean` | project-verified | Uniform exponential logarithmic-derivative majorant and absolute horizontal integrability from Mathlib's von Mangoldt series |
| `PrimeFactorUnimodality.Mathlib.Analysis.Calculus.ParametricIntervalIntegral` | `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` | project-verified | Compact-rectangle continuous derivatives supply Mathlib's dominated parameter-integral derivative hypotheses |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogNormDeriv` | `Mathlib/Analysis/SpecialFunctions/Complex/LogNormDeriv.lean` | project-verified | Branch-independent real, horizontal and vertical log-modulus derivatives from Mathlib's squared-norm derivative |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogShift` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogShift.lean` | project-verified | Exact shifted logarithmic integral and a uniform lower bound, including real-axis singularities |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.Basic` | `Mathlib/Analysis/Complex/LogStep/Basic.lean` | project-verified | Integrability, nonnegativity and conjugation invariance of unit logarithmic-modulus steps |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.SmallHeight` | `Mathlib/Analysis/Complex/LogStep/SmallHeight.lean` | project-verified | Uniform low-height integral bound using almost-everywhere comparison at the real singularity |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.LargeHeight` | `Mathlib/Analysis/Complex/LogStep/LargeHeight.lean` | project-verified | Pointwise and integrated inverse-square height decay of the logarithmic step |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.PairBound` | `Mathlib/Analysis/Complex/LogStep/PairBound.lean` | project-verified | Entirely analytic constant-sixteen paired-resolvent bound in the closed half-unit strip |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.Harmonic.EulerMascheroniBounds` | `Mathlib/NumberTheory/Harmonic/EulerMascheroniBounds.lean` | project-verified | Rational upper bound `gamma < 0.59` from Mathlib's harmonic upper sequence and logarithm bounds |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.PiBounds` | `Mathlib/Analysis/SpecialFunctions/Log/PiBounds.lean` | project-verified | Lower bounds for `log(4*pi)`, `log(2*pi)` and `log(pi)` using existing pi/log bounds and a rational logarithm inequality |
| `PrimeFactorUnimodality.Mathlib.Analysis.Calculus.Deriv.ForwardDiff` | `Mathlib/Analysis/Calculus/Deriv/ForwardDiff.lean` | project-verified | Existing Mathlib forward differences: continuity, derivatives, support norm bounds and exact binomial sample-error propagation |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.IteratedPrimitive` | `Mathlib/Analysis/SpecialFunctions/Pow/IteratedPrimitive.lean` | project-verified | Successive primitives of complex powers, finite-product denominator and imaginary-part lower bound |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDamped` | `Mathlib/Analysis/SpecialFunctions/Pow/LogDamped.lean` | project-verified | Inverse-logarithmically damped powers: derivative, global square-root bound, height monotonicity and antitonicity in the damping parameter |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedPolynomial` | `Mathlib/Analysis/SpecialFunctions/Pow/LogDampedPolynomial.lean` | project-verified | Arbitrary natural polynomial decay in the damping parameter, sacrificing one height power via two existing exponential Taylor bounds |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedShape` | `Mathlib/Analysis/SpecialFunctions/Pow/LogDampedShape.lean` | project-verified | Continuous explicit slope and derivative signs on both sides of the exact turning height |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedTail` | `Mathlib/Analysis/SpecialFunctions/Pow/LogDampedTail.lean` | project-verified | Inverse-square majorant, vanishing at infinity and monotonicity on the complete decreasing tail |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDamped` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogDamped.lean` | project-verified | Absolute integrability of damped powers, logarithmic densities and reciprocal-height corrections |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedMajorant` | `Mathlib/Analysis/SpecialFunctions/Pow/LogDampedMajorant.lean` | project-verified | Arbitrary-power splitting and selected cutoff/global-peak majorants on the entire closed tail |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogPowerTail` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogPowerTail.lean` | project-verified | Elementary primitive, absolute integrability and exact improper integral with arbitrary logarithmic offset |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedBound` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogDampedBound.lean` | project-verified | Closed density-plus-reciprocal-height bound from an integrable power majorant |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedWindow` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogDampedWindow.lean` | project-verified | Upper primitive for finite exponent-one logarithmic densities and exact exponential-cutoff evaluation |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedParameter` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogDampedParameter.lean` | project-verified | Exact cutoff feasibility, Rosser exponent choice, coefficient evaluation and elementary exponential-cutoff factors |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedSharpTail` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogDampedSharpTail.lean` | project-verified | Sharp upper primitive, finite and improper density bounds, exact exponential-cutoff coefficient, parameter equivalence, power-majorant comparison and complete fixed/growing cutoff cover |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageLocal` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageLocal.lean` | project-verified | Complex recurrence with only half-line continuity, using a continuous extension and local support congruence |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAveragePrimitive` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAveragePrimitive.lean` | project-verified | Every iterated average equals a forward difference of a successive primitive, by Mathlib FTC |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAveragePower` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAveragePower.lean` | project-verified | Exact complex-power differences and product/height decay estimates for every natural averaging order |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageScaling` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageScaling.lean` | project-verified | Exact relative-step homogeneity and fixed-coefficient phase representation on arbitrary vertical lines, including order zero. |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageConjugation` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageConjugation.lean` | project-verified | Arbitrary-order conjugation through real/imaginary box averages; conjugation of divided complex powers on positive support, including zero step. |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageStability` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageStability.lean` | project-verified | Subtraction and uniform pointwise error propagation at every averaging order, using only half-line continuity. |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageVertical` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageVertical.lean` | project-verified | Explicit vertical divided-power perturbation and averaged norm/error bounds without inverse-step amplification. |
| `PrimeFactorUnimodality.Mathlib.Analysis.Calculus.Deriv.EndpointMinimum` | `Mathlib/Analysis/Calculus/Deriv/EndpointMinimum.lean` | project-verified | Endpoint minimum when derivative nonpositivity persists; reuses Mathlib mean-value monotonicity |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.SingleCrossing` | `Mathlib/Analysis/Complex/FiniteLaplace/SingleCrossing.lean` | project-verified | Real transform differentiation reuses the entire finite Laplace proof; signed single-crossing sources have endpoint minima |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.Autocorrelation` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Autocorrelation.lean` | project-verified | Exact cosine sum-of-squares identity; global phase nonnegativity and linear-size correlation formulas |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.AffineRatio` | `Mathlib/Analysis/SpecialFunctions/Log/AffineRatio.lean` | project-verified | Monotonicity and endpoint bounds for `log t / log (a*t+b)` on `t>1`, for `a>=1`, `b>=0` |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.JensenAverage` | `Mathlib/Analysis/Complex/JensenAverage.lean` | project-verified | Jensen divisor comparison retaining the actual circle average, extracted from Mathlib's supremum-bound proof |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.CircleAverageAntipodal` | `Mathlib/MeasureTheory/Integral/CircleAverageAntipodal.lean` | project-verified | Antipodal invariance, integrability, and circle bounds from opposite-point pairs |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.Trapezoid` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Trapezoid.lean` | project-verified | Exact complex trapezoid remainder and integral second-derivative norm bound |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogTrapezoid` | `Mathlib/Analysis/SpecialFunctions/Complex/LogTrapezoid.lean` | project-verified | Horizontal logarithm integral, finite-sum identity, and height-independent telescoping remainder |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogShiftLimit` | `Mathlib/Analysis/SpecialFunctions/Complex/LogShiftLimit.lean` | project-verified | Vanishing endpoint phase and full complex shifted-log normalization limits |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral` | `Mathlib/MeasureTheory/Integral.lean` | project-verified | Facade grouping reusable integral candidates |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerLog` | `Mathlib/NumberTheory/LSeries/RiemannZetaEulerLog.lean` | project-verified | Analytic Euler logarithm from Mathlib's Euler product, real-axis norm majorant, and lower zeta modulus bound |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.HorizontalDecay` | `Mathlib/NumberTheory/LSeries/HorizontalDecay.lean` | project-verified | Termwise and complete-series horizontal decay from a positive lower support bound |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerDecay` | `Mathlib/NumberTheory/LSeries/RiemannZetaEulerDecay.lean` | project-verified | Exponential decay of the actual Euler logarithm and two-sided log modulus using its vanishing unit coefficient |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogIntegral` | `Mathlib/NumberTheory/LSeries/RiemannZetaLogIntegral.lean` | project-verified | Finite horizontal log integrability across zeros, absolute integrability of the infinite tail, and an explicit uniform tail bound |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries` | `Mathlib/NumberTheory/LSeries.lean` | project-verified | Facade grouping the independently reusable Dirichlet-series modules |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.Interval` | `Mathlib/Analysis/Complex/Log/Interval.lean` | project-verified | Continuous logarithm along a closed real interval with prescribed initial value, using the exponential covering |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.IntervalIntegral` | `Mathlib/Analysis/Complex/Log/IntervalIntegral.lean` | project-verified | Derivative and exact integral increment of an arbitrary continuous logarithm along a real interval |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.ZeroCount` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/ZeroCount.lean` | project-verified | Endpoint phase change bounded by the finite cosine-zero count using the intermediate value theorem |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.JensenCard` | `Mathlib/Analysis/Complex/JensenCard.lean` | project-verified | Finite distinct zeros and their cardinality bound by the analytic divisor mass on compact connected domains |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Powers.Recurrence` | `Mathlib/Analysis/Complex/Powers/Recurrence.lean` | project-verified | Unbounded powers of a unit complex number return to one; arbitrarily large powers have quantitatively positive real parts |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Exp.Cubic` | `Mathlib/Analysis/SpecialFunctions/Exp/Cubic.lean` | project-verified | Mathlib exponential series and summable order comparison |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Exp.Monomial` | `Mathlib/Analysis/SpecialFunctions/Exp/Monomial.lean` | project-verified | Damped natural monomials decrease from their exact turning point and attain a global maximum there; reuses logarithmic inequalities, including order-zero monotonicity and a zero input to the maximum bound |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow` | `Mathlib/Analysis/SpecialFunctions/Pow.lean` | project-verified | Facade grouping reusable power candidates without project imports |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpMoments` | `Mathlib/Analysis/SpecialFunctions/Integrals/ExpMoments.lean` | project-verified | Mathlib finite-interval comparison and linearity |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpLinear` | `Mathlib/Analysis/SpecialFunctions/Integrals/ExpLinear.lean` | project-verified | Reuses Mathlib `integral_exp_mul_complex`; FTC evaluates the linear weight and both zero-exponent branches |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpTrig` | `Mathlib/Analysis/SpecialFunctions/Integrals/ExpTrig.lean` | project-verified | Real and imaginary parts of the exact complex exponential integrals; explicit real endpoint formulas |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair` | `Mathlib/Analysis/SpecialFunctions/Integrals/ReciprocalSquarePair.lean` | project-verified | Continuity, monotonicity, and explicit divided-pair improper integral bounds |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogReciprocalSquarePair` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogReciprocalSquarePair.lean` | project-verified | Exact logarithmic paired reciprocal-square improper integral; integrability permits sign changes and arbitrary real logarithmic offsets |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions` | `Mathlib/Analysis/SpecialFunctions.lean` | project-verified | Facade grouping special-function candidates without changing their individual import boundaries |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.FinsetAbel` | `Mathlib/MeasureTheory/Integral/FinsetAbel.lean` | project-verified | Weighted Abel summation at arbitrary real locations; exact clipped cumulative-count integral, retaining repeated labels, early locations and both endpoints |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IoiTranslation` | `Mathlib/MeasureTheory/Integral/IoiTranslation.lean` | project-verified | Improper-integral translation and actual integrability via Mathlib's measure-preserving API |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairWeighted` | `Mathlib/Analysis/SpecialFunctions/Integrals/ReciprocalSquarePairWeighted.lean` | project-verified | Derivative-weight majorants, logarithmic integrability and integration by parts with an arbitrary additive constant, and vanishing logarithmic and linear-log boundaries |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.WeightedBounds` | `Mathlib/Analysis/Complex/FiniteLaplace/WeightedBounds.lean` | project-verified | Mathlib norm-integral comparison |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.OuterStrip` | `Mathlib/Analysis/Complex/Poisson/OuterStrip.lean` | project-verified | Signed rational comparison and a uniform height cutoff inside the critical strip |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.Reciprocal` | `Mathlib/Analysis/Complex/Poisson/Reciprocal.lean` | project-verified | Inverse-height square domination by paired real reciprocal kernels throughout the closed strip |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Series.Imaginary` | `Mathlib/Analysis/Complex/Series/Imaginary.lean` | project-verified | Explicit inverse-square domination on separated vertical strips |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity` | `Mathlib/Analysis/Complex/FiniteLaplace/Monotonicity.lean` | project-verified | Mathlib real-part integration and pointwise integral comparison |
| `PrimeFactorUnimodality.Mathlib.Topology.Algebra.InfiniteSum.Paired` | `Mathlib/Topology/Algebra/InfiniteSum/Paired.lean` | project-verified | Mathlib finite-subsum bound and equivalence reindexing |
| `PrimeFactorUnimodality.Mathlib.Topology.Algebra.InfiniteSum.Sublevel` | `Mathlib/Topology/Algebra/InfiniteSum/Sublevel.lean` | project-verified | Sublevel exhaustion and vanishing monotone-weight counting boundary from dominated convergence |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairDeriv` | `Mathlib/Analysis/SpecialFunctions/Integrals/ReciprocalSquarePairDeriv.lean` | project-verified | Explicit derivative and decay of the paired reciprocal squares away from both poles |
| `PrimeFactorUnimodality.Mathlib.Analysis.Analytic.Order.Conjugation` | `Mathlib/Analysis/Analytic/Order/Conjugation.lean` | project-verified | PNT `Kadiri.analyticAt_conj_conj` / `Kadiri.analyticOrderAt_conj_conj`, revision `f6147e7572ab3abe5428101bc0b13627bcb005df`; BV `ComplexAnalysis.AnalyticAt.{conj_conj,analyticOrderAt_conj_conj,analyticOrderNatAt_conj_conj}`, revision `7a1748306e026825ed6a5555516cc2f28989b2ac`; Apache-2.0, Mathlib-only extraction, derivative helper replaced by Mathlib |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex` | `Mathlib/Analysis/Complex.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.ThreeKernelUniform` | `Mathlib/Analysis/Complex/Poisson/ThreeKernelUniform.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedStrip` | `Mathlib/Analysis/Complex/FiniteLaplace/PairedStrip.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.RealSource` | `Mathlib/Analysis/Complex/FiniteLaplace/RealSource.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.PhragmenLindelof.RealPart` | `Mathlib/Analysis/Complex/PhragmenLindelof/RealPart.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson` | `Mathlib/Analysis/Complex/Poisson.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.ThreeKernel` | `Mathlib/Analysis/Complex/Poisson/ThreeKernel.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerChunk` | `Mathlib/Algebra/Group/PowerChunk.lean` | extracting | None |
| `PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerStep` | `Mathlib/Algebra/Group/PowerStep.lean` | extracting | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace` | `Mathlib/Analysis/Complex/FiniteLaplace.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals` | `Mathlib/Analysis/SpecialFunctions/Integrals.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.CorrelationBound` | `Mathlib/Analysis/SpecialFunctions/Integrals/CorrelationBound.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.CosineCorrelation` | `Mathlib/Analysis/SpecialFunctions/Integrals/CosineCorrelation.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic` | `Mathlib/Analysis/Complex/FiniteLaplace/Basic.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Bounds` | `Mathlib/Analysis/Complex/FiniteLaplace/Bounds.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Continuity` | `Mathlib/Analysis/Complex/FiniteLaplace/Continuity.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.ContourBounds` | `Mathlib/Analysis/Complex/FiniteLaplace/ContourBounds.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Correlation` | `Mathlib/Analysis/Complex/FiniteLaplace/Correlation.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Differentiability` | `Mathlib/Analysis/Complex/FiniteLaplace/Differentiability.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.DirichletIntegral` | `Mathlib/Analysis/Complex/FiniteLaplace/DirichletIntegral.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Inversion` | `Mathlib/Analysis/Complex/FiniteLaplace/Inversion.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedBounds` | `Mathlib/Analysis/Complex/FiniteLaplace/PairedBounds.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedSeries` | `Mathlib/Analysis/Complex/FiniteLaplace/PairedSeries.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.RemainderSource` | `Mathlib/Analysis/Complex/FiniteLaplace/RemainderSource.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.ResolventIntegral` | `Mathlib/Analysis/Complex/FiniteLaplace/ResolventIntegral.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.RightResolventIntegral` | `Mathlib/Analysis/Complex/FiniteLaplace/RightResolventIntegral.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Summability` | `Mathlib/Analysis/Complex/FiniteLaplace/Summability.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Scaling` | `Mathlib/Analysis/Complex/FiniteLaplace/Scaling.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.VolterraEnergy` | `Mathlib/Analysis/Complex/FiniteLaplace/VolterraEnergy.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.Triangle` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Triangle.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverage` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverage.lean` | project-verified | Arbitrary iterated averages of discontinuous monotone functions; exact half-width error correction |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageAlgebra` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageAlgebra.lean` | project-verified | Scalar and finite-sum identities for every averaging order |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageContinuous` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageContinuous.lean` | project-verified | Continuity and constant subtraction for nonmonotone continuous inputs |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageComplex` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageComplex.lean` | project-verified | Complex averages, local support congruence, and sharp support norm bounds |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ComplexDecay` | `Mathlib/Analysis/SpecialFunctions/Pow/ComplexDecay.lean` | project-verified | BV real-part-gap power bound, with Mathlib-only imports and positive-half-line continuity |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageRegularity` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageRegularity.lean` | project-verified | Each additional average of a monotone function gains a continuous derivative |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageSupport` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IteratedAverageSupport.lean` | project-verified | Translation and dependence only on the finite averaging support |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.Integral` | `Mathlib/Analysis/Complex/Hadamard/Integral.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.IntegralBounds` | `Mathlib/Analysis/Complex/Hadamard/IntegralBounds.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Cauchy` | `Mathlib/Analysis/Complex/Integrability/Cauchy.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Resolvent` | `Mathlib/Analysis/Complex/Integrability/Resolvent.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.RightResolvent` | `Mathlib/Analysis/Complex/Integrability/RightResolvent.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.Stechkin` | `Mathlib/Analysis/Complex/Poisson/Stechkin.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaConjugation` | `Mathlib/Analysis/SpecialFunctions/Gamma/DigammaConjugation.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.HalfIntegerNorm` | `Mathlib/Analysis/SpecialFunctions/Gamma/HalfIntegerNorm.lean` | project-verified | Exact half-line norm and polynomial bounds from reflection and recurrence |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrability.LogCauchy` | `Mathlib/Analysis/SpecialFunctions/Integrability/LogCauchy.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.Deriv` | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ThreeHalves` | `Mathlib/Analysis/SpecialFunctions/Pow/ThreeHalves.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Data.Nat.Periodic` | `Mathlib/Data/Nat/Periodic.lean` | extracting | None |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.Bochner.Series` | `Mathlib/MeasureTheory/Integral/Bochner/Series.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.BLSPrimality` | `Mathlib/NumberTheory/BLSPrimality.lean` | extracting | None |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.VerticalIntegral` | `Mathlib/NumberTheory/LSeries/VerticalIntegral.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.ZetaTrigonometric` | `Mathlib/NumberTheory/LSeries/ZetaTrigonometric.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.ZetaTrigonometricShift` | `Mathlib/NumberTheory/LSeries/ZetaTrigonometricShift.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington` | `Mathlib/NumberTheory/Pocklington.lean` | extracting | None |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.PrimalityCongruence` | `Mathlib/NumberTheory/PrimalityCongruence.lean` | extracting | None |
| `PrimeFactorUnimodality.Mathlib.Data.Nat.CoprimePeriodicCount` | `Mathlib/Data/Nat/CoprimePeriodicCount.lean` | extracting | None |

Readiness should be one of: `extracting`, `project-verified`, `mathlib-ready`,
`submitted`, or `upstreamed`. A module is `mathlib-ready` only after it has an
identified destination, no project dependency, focused tests, and a clean
standalone build against the project's pinned Mathlib revision.
