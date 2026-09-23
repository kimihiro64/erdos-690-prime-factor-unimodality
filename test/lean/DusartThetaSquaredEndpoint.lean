import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaSquaredEndpoint

/-! # Reduced-cutoff interfaces and real-endpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real Set MeasureTheory

example {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x) (hlog : Real.log x ≤ 85)
    (hp : |Chebyshev.psi x - x| / x < (1 / 36260 : ℝ)) :
    |Chebyshev.theta x - x| < (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_lt_logSquared_of_psi_endpoint hx hlog hp

example {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x) (hlog : Real.log x ≤ 85)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| < (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_lt_logSquared_of_reduced_endpoint_band hx hlog hgap

example {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x) (hlog : Real.log x ≤ 85)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| < (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_lt_logSquared_of_endpoint_band hx hlog hgap

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (tail : HasThetaLogSquaredError (1 / 5) (Real.exp 85))
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_reduced_endpoint_band_and_tail finite tail hgap

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (tail : HasThetaLogSquaredError (1 / 5) (Real.exp 85))
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_endpoint_band_and_tail finite tail hgap



end

end PrimeFactorUnimodality.Tests
