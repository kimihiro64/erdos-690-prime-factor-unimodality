import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaSquaredEndpoint

/-! # Regression statements for the direct log-square Dusart route -/

namespace PrimeFactorUnimodality.Tests

example {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x) (hlog : Real.log x ≤ 85)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| < (1 / 5 : ℝ) * x / Real.log x ^ 2 :=
  abs_theta_sub_lt_logSquared_of_endpoint_band hx hlog hgap

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (tail : HasThetaLogSquaredError (1 / 5) (Real.exp 85))
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_endpoint_band_and_tail finite tail hgap

end PrimeFactorUnimodality.Tests
