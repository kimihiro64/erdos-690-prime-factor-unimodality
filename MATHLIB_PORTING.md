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
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerLog` | `Mathlib/NumberTheory/LSeries/RiemannZetaEulerLog.lean` | project-verified | Analytic Euler logarithm from Mathlib's Euler product, real-axis norm majorant, and lower zeta modulus bound |
| `PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries` | `Mathlib/NumberTheory/LSeries.lean` | project-verified | Facade grouping the independently reusable Dirichlet-series modules |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.Interval` | `Mathlib/Analysis/Complex/Log/Interval.lean` | project-verified | Continuous logarithm along a closed real interval with prescribed initial value, using the exponential covering |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.IntervalIntegral` | `Mathlib/Analysis/Complex/Log/IntervalIntegral.lean` | project-verified | Derivative and exact integral increment of an arbitrary continuous logarithm along a real interval |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.ZeroCount` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/ZeroCount.lean` | project-verified | Endpoint phase change bounded by the finite cosine-zero count using the intermediate value theorem |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.JensenCard` | `Mathlib/Analysis/Complex/JensenCard.lean` | project-verified | Finite distinct zeros and their cardinality bound by the analytic divisor mass on compact connected domains |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Powers.Recurrence` | `Mathlib/Analysis/Complex/Powers/Recurrence.lean` | project-verified | Unbounded powers of a unit complex number return to one; arbitrarily large powers have quantitatively positive real parts |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Exp.Cubic` | `Mathlib/Analysis/SpecialFunctions/Exp/Cubic.lean` | project-verified | Mathlib exponential series and summable order comparison |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpMoments` | `Mathlib/Analysis/SpecialFunctions/Integrals/ExpMoments.lean` | project-verified | Mathlib finite-interval comparison and linearity |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair` | `Mathlib/Analysis/SpecialFunctions/Integrals/ReciprocalSquarePair.lean` | project-verified | Continuity, monotonicity, and explicit divided-pair improper integral bounds |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogReciprocalSquarePair` | `Mathlib/Analysis/SpecialFunctions/Integrals/LogReciprocalSquarePair.lean` | project-verified | Exact logarithmic paired reciprocal-square improper integral; integrability permits sign changes and arbitrary real logarithmic offsets |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions` | `Mathlib/Analysis/SpecialFunctions.lean` | project-verified | Facade grouping special-function candidates without changing their individual import boundaries |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.FinsetAbel` | `Mathlib/MeasureTheory/Integral/FinsetAbel.lean` | project-verified | Weighted Abel summation at arbitrary real locations, preserving repeated labels and both interval endpoints |
| `PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IoiTranslation` | `Mathlib/MeasureTheory/Integral/IoiTranslation.lean` | project-verified | Improper-integral translation and actual integrability via Mathlib's measure-preserving API |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairWeighted` | `Mathlib/Analysis/SpecialFunctions/Integrals/ReciprocalSquarePairWeighted.lean` | project-verified | Derivative-weight majorants, logarithmic integrability and integration by parts, and vanishing logarithmic and linear-log boundaries |
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
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.Integral` | `Mathlib/Analysis/Complex/Hadamard/Integral.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.IntegralBounds` | `Mathlib/Analysis/Complex/Hadamard/IntegralBounds.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Cauchy` | `Mathlib/Analysis/Complex/Integrability/Cauchy.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Resolvent` | `Mathlib/Analysis/Complex/Integrability/Resolvent.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.RightResolvent` | `Mathlib/Analysis/Complex/Integrability/RightResolvent.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.Stechkin` | `Mathlib/Analysis/Complex/Poisson/Stechkin.lean` | project-verified | None |
| `PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaConjugation` | `Mathlib/Analysis/SpecialFunctions/Gamma/DigammaConjugation.lean` | project-verified | None |
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
