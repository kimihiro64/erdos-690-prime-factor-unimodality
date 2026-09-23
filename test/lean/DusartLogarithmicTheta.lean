import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicTheta

/-! # Regression statements for the decreasing logarithmic error -/

namespace PrimeFactorUnimodality.Tests

open Real

example {x : ℝ} (hx : 1 ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ 18 * exp (-Real.log x / 2) :=
  dusartThetaRootRelativeCorrection_le_half_exp hx

example {x : ℝ}
    (hx : 1 < x) (hb : 100 ≤ Real.log x) :
    dusartThetaRootRelativeCorrection x ≤ (1 / 100 : ℝ) / Real.log x :=
  dusartThetaRootRelativeCorrection_le_logarithmic hx hb

example {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ (3 / 200000 : ℝ) :=
  dusartThetaRootRelativeCorrection_endpoint_le hx

example {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    Chebyshev.theta x - x < x / 36260 ∧
      |Chebyshev.theta x - x| < (12323 / 10000 : ℝ) * x / Real.log x :=
  dusartTheta_margins_of_billion_low_gap hx hgap

example
    (finite : HasDusartSymmetricThetaBoundsBelow 1441000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : HasDusartThetaBounds :=
  hasDusartThetaBounds_of_finite_and_billion_low_gap finite hgap

end PrimeFactorUnimodality.Tests
