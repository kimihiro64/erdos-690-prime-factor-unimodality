import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGridError
import PrimeFactorUnimodality.Helpers.Analytic.XiGridSignIntervals
import PrimeFactorUnimodality.Helpers.Analytic.XiSimplePhaseIntervals

/-! # Shared configuration for executable xi sign samples

All long checks and transcendental constants are certified once per block.
The validity fields are precisely the already-proved moment/Fourier,
endpoint, interval and shared-budget interfaces. No zero or sign is a field.
The remaining sample check is a short rational calculation.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core Polynomial

/-- Constants and retained arrays reused by every short sign check in a block. -/
structure SharedXiGridCheck where
  rows : RationalGridRows
  model : ZetaGroupedBlock
  errors : RationalGridErrorBudget
  endpoint : DirichletEndpointIntervals
  scalar : SharedTaylorIntervals
  phaseData : XiSimplePhaseIntervals
  pi : IntervalRat
  base : IntervalRat
  radius : IntervalRat
  expHalf : IntervalRat
  coefficients : List ℚ
  bernoulliCap : ℚ

namespace SharedXiGridCheck

/-- The same mathematical grid used by the existing actual-zeta and xi proofs. -/
def grid (c : SharedXiGridCheck) : ZetaGridBlock := c.rows.attach c.model

/-- Independently established shared obligations, checked once rather than per sample. -/
structure Valid (c : SharedXiGridCheck) : Prop where
  grid : c.grid.Valid
  moments : ∀ k j, c.model.coefficientError k j = (c.errors.moment k j : ℝ)
  endpoint : c.endpoint.Valid
  cutoff : c.endpoint.cutoff = c.model.cutoff
  scalar : c.scalar.Prepared
  phase : c.phaseData.Valid
  pi : Real.pi ∈ c.pi
  base : c.model.base ∈ c.base
  radius : c.model.radius ∈ c.radius
  exponential : Real.exp (1 / 2) ∈ c.expHalf
  budget : c.errors.check c.rows c.model.cutoff c.model.degree c.expHalf = true
  coefficients : c.coefficients = eulerBernoulliCoefficients 1 c.model.order
  bernoulli : c.bernoulliCap = bernoulliCoeffBudget (c.model.order + 1)

/-- The exact same enclosed height feeds correction, phase and remainder calculations. -/
def height (c : SharedXiGridCheck) (p : RationalGridPoint) : IntervalRat :=
  p.heightInterval c.rows.levels c.pi c.base c.radius

/-- Actual grid heights belong to the common per-sample interval. -/
theorem mem_height {c : SharedXiGridCheck} (hc : c.Valid) (p : RationalGridPoint) :
    p.toGridPoint.height c.grid ∈ c.height p :=
  IntervalRat.mem_add hc.base (IntervalRat.mem_mul hc.radius
    (mem_zetaGridCoordinateInterval hc.pi c.rows.levels p.index))

/-- All remaining per-sample obligations are executable rational tests. -/
def check (c : SharedXiGridCheck) (s : XiGridSignData) : Bool :=
  s.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius c.coefficients &&
    c.phaseData.check c.scalar (c.height s.point) s.phase s.phaseError &&
    checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap &&
    s.checkMargin c.rows c.model.degree c.scalar c.pi c.errors.cap

end SharedXiGridCheck

end PrimeFactorUnimodality
