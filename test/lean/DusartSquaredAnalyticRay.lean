import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAnalyticRay

/-! # Regression statements for the middle-range Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) (exp 85) := by
  apply PrimeFactorUnimodality.hasThetaLogSquaredError_above_exp85 <;> assumption

example
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  apply PrimeFactorUnimodality.hasThetaLogSquaredError_above_endpoint <;> assumption

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  apply PrimeFactorUnimodality.hasThetaLogSquaredError_of_lower_band_and_zero_data <;> assumption

end PrimeFactorUnimodality.Tests
