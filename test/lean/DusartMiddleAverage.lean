import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleAverage

/-! # Regression statements for the middle-range Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {s x : ℝ}
    (hx : 1 < x) (hb : 84 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hs₀ : (3 / 40 : ℝ) / Real.log x ^ 2 ≤ s)
    (hs₁ : s ≤ (17 / 200 : ℝ) / Real.log x ^ 2) :
    dusartBoxRosserFixedRelativeBudget 0 s x 6 2 10 1000000000 (1 / 2) ≤
      (3 / 50 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.dusartBoxRosserFixedRelativeBudget_le_middle <;> assumption

example {s x : ℝ}
    (hx : 1 < x) (hb : 84 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hs₀ : (3 / 40 : ℝ) / Real.log x ^ 2 ≤ s)
    (hs₁ : s ≤ (17 / 200 : ℝ) / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError 3 (s * x) x| / x ≤ (3 / 50 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.abs_dusartPsiAverageError_div_le_middle <;> assumption

end PrimeFactorUnimodality.Tests
