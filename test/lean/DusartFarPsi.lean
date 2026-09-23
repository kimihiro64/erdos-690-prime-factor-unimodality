import PrimeFactorUnimodality.Helpers.Analytic.DusartFarPsi

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.psi x - x| / x ≤ (1 / 20 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.abs_psi_sub_div_le_far <;> assumption

end PrimeFactorUnimodality.Tests
