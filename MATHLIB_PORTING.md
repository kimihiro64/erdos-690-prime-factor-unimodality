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
