import PrimeFactorUnimodality.Helpers.Analytic.DusartBillionCutoffTheta
import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAnalyticRay

/-! # The complete analytic theta ray from three billion

The early intervals join the existing infinite ray without strengthening
its zero-data assumptions. Consequently the published cutoff needs finite
theta data only up to three billion; the coefficient and conclusion are unchanged.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The original billion-height premise includes the shorter early-interval premise. -/
theorem dusartEarlier_low_zero_restriction
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ) := by
  intro z hz
  apply hgap z
  rw [mem_xiLowHeightIndices] at hz ⊢
  exact hz.trans_le (by norm_num)

/-- Analytic coverage starts at three billion and extends through every larger real point. -/
theorem hasThetaLogSquaredError_above_earlier_cutoff
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 3000000000 := by
  intro x hx
  by_cases h : x ≤ 1441000000000
  · exact abs_theta_sub_le_logSquared_billion_bridge hx h (dusartEarlier_low_zero_restriction hgap)
  · exact hasThetaLogSquaredError_above_endpoint hgap hreg x (le_of_not_ge h)

/-- The exact published theorem needs finite input only through three billion. -/
theorem hasThetaLogSquaredError_of_earlier_band_and_zero_data
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  intro x hx
  by_cases h : x ≤ 3000000000
  · exact finite x hx h
  · exact hasThetaLogSquaredError_above_earlier_cutoff hgap hreg x (le_of_not_ge h)

end

end PrimeFactorUnimodality
