import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleTail

/-! # Regression statements for the middle-range Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example :
    (207 / 10 : ℝ) ≤ Real.log 1000000000 ∧ Real.log 1000000000 ≤ 21 := by
  apply PrimeFactorUnimodality.dusartMiddle_log_billion_bounds <;> assumption

example {b : ℝ} (hb : b ≤ 5000) :
    exp (sqrt ((b / 6) / (4 - 2))) ≤ (1000000000 : ℝ) := by
  apply PrimeFactorUnimodality.dusartMiddle_cutoff_branch <;> assumption

example {b U : ℝ} (hU : 0 < U)
    (hpeak : exp (sqrt ((b / 6) / (4 - 2))) ≤ U) :
    xiRosserClosedTailBound (b / 6) 4 2 U =
      ((Real.log (U / (2 * π)) + 1) / (π * U ^ 3) +
        (4 * Real.log U + 69) / U ^ 4) * exp (-b / (6 * Real.log U)) := by
  apply PrimeFactorUnimodality.xiRosserClosedTailBound_four_two_eq <;> assumption

example :
    (Real.log ((1000000000 : ℝ) / (2 * π)) + 1) / (π * 1000000000 ^ 3) +
      (4 * Real.log 1000000000 + 69) / 1000000000 ^ 4 ≤ (7 / 10 ^ 27 : ℝ) := by
  apply PrimeFactorUnimodality.dusartMiddle_tail_coefficient_le <;> assumption

example {b : ℝ} (hb : 0 ≤ b) (hb₁ : b ≤ 5000) :
    xiRosserClosedTailBound (b / 6) 4 2 1000000000 ≤
      (7 / 10 ^ 27 : ℝ) * exp (-b / 126) := by
  apply PrimeFactorUnimodality.xiRosserClosedTailBound_middle_le <;> assumption

example : exp (sqrt (((5000 : ℝ) / 6) / (4 - 2))) ≤ (1000000000 : ℝ) :=
  dusartMiddle_cutoff_branch le_rfl

example : xiRosserClosedTailBound ((84 : ℝ) / 6) 4 2 1000000000 ≤
    (7 / 10 ^ 27 : ℝ) * exp (-84 / 126) :=
  xiRosserClosedTailBound_middle_le (by norm_num) (by norm_num)

end PrimeFactorUnimodality.Tests
