import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoff

/-! # Earlier analytic cutoff interfaces and seam regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ) := by
  exact PrimeFactorUnimodality.dusartEarlier_low_zero_restriction hgap

example
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 10000000000 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_above_earlier_cutoff hgap hreg

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 10000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_earlier_band_and_zero_data finite hgap hreg



end

end PrimeFactorUnimodality.Tests
