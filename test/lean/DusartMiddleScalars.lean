import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleScalars

/-! # Regression statements for the middle-range Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {b : ℝ} (hb : 0 ≤ b) :
    b ^ 8 * exp (-b / 126) ≤ (1008 : ℝ) ^ 8 / 2500 := by
  apply PrimeFactorUnimodality.dusartMiddle_eighth_moment_le <;> assumption

example {b s : ℝ} (hb : 84 ≤ b)
    (hs : s ≤ (17 / 200 : ℝ) / b ^ 2) : 1 + 3 * s ≤ (10001 / 10000 : ℝ) := by
  apply PrimeFactorUnimodality.dusartMiddle_width_le <;> assumption

example {b s : ℝ} (hb : 84 ≤ b)
    (hs₀ : (3 / 40 : ℝ) / b ^ 2 ≤ s) (hs₁ : s ≤ (17 / 200 : ℝ) / b ^ 2) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ (202 / 25 : ℝ) / ((3 / 40 : ℝ) / b ^ 2) ^ 3 := by
  apply PrimeFactorUnimodality.dusartMiddle_high_coefficient_le <;> assumption

example {b s : ℝ} (hb : 84 ≤ b) (hb₁ : b ≤ 5000)
    (hs₀ : (3 / 40 : ℝ) / b ^ 2 ≤ s) (hs₁ : s ≤ (17 / 200 : ℝ) / b ^ 2) :
    b ^ 2 * ((8 * (1 + 3 * s) ^ 4 / s ^ 3) *
      xiRosserClosedTailBound (b / 6) 4 2 1000000000) ≤ (59 / 1000 : ℝ) := by
  apply PrimeFactorUnimodality.dusartMiddle_high_moment_le <;> assumption

example {b : ℝ} (hb : 84 ≤ b) :
    b ^ 2 * (77 * exp (-b / 2)) ≤ (1 / 10000 : ℝ) := by
  apply PrimeFactorUnimodality.dusartMiddle_low_moment_le <;> assumption

example {b : ℝ} (hb : 84 ≤ b) :
    b ^ 2 * (4 / exp b) ≤ (1 / 10000 : ℝ) := by
  apply PrimeFactorUnimodality.dusartMiddle_correction_moment_le <;> assumption

example : (1008 : ℝ) ^ 8 * exp (-1008 / 126) ≤ (1008 : ℝ) ^ 8 / 2500 :=
  dusartMiddle_eighth_moment_le (by norm_num)

example : (84 : ℝ) ^ 2 * (77 * exp (-84 / 2)) ≤ (1 / 10000 : ℝ) :=
  dusartMiddle_low_moment_le le_rfl

end PrimeFactorUnimodality.Tests
