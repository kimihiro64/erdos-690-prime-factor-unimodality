import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGridError

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open Fourier
open Polynomial
open PrimeFactorUnimodality.RationalGridPoint

example (p : RationalGridPoint) (r : RationalGridRows)
    (d : ZetaGroupedBlock) (hg : (r.attach d).Valid)
    (b : RationalGridErrorBudget) (hm : ∀ k j, d.coefficientError k j = (b.moment k j : ℝ))
    {expHalf : IntervalRat} (he : Real.exp (1 / 2) ∈ expHalf)
    (hb : b.check r d.cutoff d.degree expHalf = true)
    {endpoint : DirichletEndpointIntervals} (hd : endpoint.Valid) (hN : endpoint.cutoff = d.cutoff)
    {P B R : IntervalRat} (hpi : Real.pi ∈ P) (hbase : d.base ∈ B) (hradius : d.radius ∈ R)
    (hw : intervalWithinUnit (zetaGridCoordinateInterval P r.levels p.index) = true)
    {C M E : ℚ} (hC : C = bernoulliCoeffBudget (d.order + 1))
    (hE : checkEulerRemainder endpoint
      (ZetaCorrectionIntervals.critical (p.heightInterval r.levels P B R)) d.order C M E = true) :
    p.toGridPoint.error (r.attach d) ≤ ((E + b.cap + p.error : ℚ) : ℝ) := by
  exact PrimeFactorUnimodality.RationalGridPoint.error_le_of_checks p r d hg b hm he hb hd hN hpi hbase hradius hw hC hE



end

end PrimeFactorUnimodality.Tests
