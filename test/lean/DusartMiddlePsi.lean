import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddlePsi

/-! # Regression statements for the middle-range Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {x : ℝ}
    (hx : 1 < x) (hb : 85 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.psi x - x| / x ≤ (19 / 100 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.abs_psi_sub_div_le_middle <;> assumption

end PrimeFactorUnimodality.Tests
