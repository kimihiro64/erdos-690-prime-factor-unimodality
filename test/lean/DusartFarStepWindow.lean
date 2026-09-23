import PrimeFactorUnimodality.Helpers.Analytic.DusartFarStepWindow

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {X s : ℝ} (hX : 28 ≤ X)
    (hs : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) : 1 + 3 * s ≤ (11 / 10 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_width_le <;> assumption

example {X s : ℝ} (hX : 28 ≤ X) (hs : 0 < s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) :
    (1 + 3 * s) * (2 * xiRosserNuWindowBound X (4 / 5)) ≤
      32 * X * exp (-(5 / 4 : ℝ) * X) := by
  apply PrimeFactorUnimodality.dusartFar_window_le <;> assumption

example {X s : ℝ} (hX : 28 ≤ X)
    (hs₀ : exp (-(4 / 5 : ℝ) * X) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ 128 / exp (-(4 / 5 : ℝ) * X) ^ 3 := by
  apply PrimeFactorUnimodality.dusartFar_high_coefficient_le <;> assumption

example {X s : ℝ} (hX : 28 ≤ X)
    (hs₀ : exp (-(4 / 5 : ℝ) * X) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) :
    (8 * (1 + 3 * s) ^ 4 / s ^ 3) * xiRosserSharpTailBound X 3 (4 / 5) ≤
      2048 * X * exp (-(5 / 4 : ℝ) * X) := by
  apply PrimeFactorUnimodality.dusartFar_high_le <;> assumption

end PrimeFactorUnimodality.Tests
