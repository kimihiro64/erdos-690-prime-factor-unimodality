import PrimeFactorUnimodality.Helpers.Analytic.DusartFarTheta

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {x : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x) :
    dusartThetaRootRelativeCorrection x ≤ (1 / 500 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.dusartThetaRootRelativeCorrection_le_far <;> assumption

example {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.abs_theta_sub_le_logSquared_far <;> assumption

example
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) (exp 5000) := by
  apply PrimeFactorUnimodality.hasThetaLogSquaredError_far <;> assumption

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (middle : ∀ x : ℝ, exp 85 ≤ x → x ≤ exp 5000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  apply PrimeFactorUnimodality.hasThetaLogSquaredError_of_bands_and_zero_data <;> assumption

end PrimeFactorUnimodality.Tests
