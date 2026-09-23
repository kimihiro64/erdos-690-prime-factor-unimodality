import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicAverage

/-! # Regression statements for the decreasing logarithmic error -/

namespace PrimeFactorUnimodality.Tests

open Real

example {s x : ℝ}
    (hx : 1 < x) (hb : 50 ≤ Real.log x)
    (hs₀ : 1 / (60 * Real.log x) ≤ s) (hs₁ : s ≤ 1 / (20 * Real.log x)) :
    ‖dusartBoxXiHighSum 0 (s * x) x 1000000000‖ / x ≤
      (3 / 50 : ℝ) / Real.log x :=
  norm_dusartBoxXiHighSum_div_le_logarithmic hx hb hs₀ hs₁

example {s x : ℝ}
    (hx : 1 < x) (hb : 50 ≤ Real.log x)
    (hs₀ : 1 / (60 * Real.log x) ≤ s) (hs₁ : s ≤ 1 / (20 * Real.log x))
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |dusartPsiAverageError 3 (s * x) x| / x ≤ 1 / (2 * Real.log x) :=
  abs_dusartPsiAverageError_div_le_logarithmic hx hb hs₀ hs₁ hgap

end PrimeFactorUnimodality.Tests
