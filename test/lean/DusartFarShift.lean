import PrimeFactorUnimodality.Helpers.Analytic.DusartFarShift

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {b c : ℝ} (hc : 4704 ≤ c)
    (hcb : c ≤ b) (hbc : b ≤ c + 1) :
    exp (-(4 / 5 : ℝ) * sqrt (b / 6)) ≤ exp (-(4 / 5 : ℝ) * sqrt (c / 6)) ∧
      exp (-(4 / 5 : ℝ) * sqrt (c / 6)) ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (b / 6)) := by
  apply PrimeFactorUnimodality.dusartFar_step_shift_le <;> assumption

example {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x) :
    let s := exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))
    let t := 1 - 3 * s
    (1 / 2 : ℝ) ≤ t ∧ t ≤ 1 ∧ 1 < x * t ∧
      Real.log x - 1 ≤ Real.log (x * t) ∧ Real.log (x * t) ≤ Real.log x := by
  apply PrimeFactorUnimodality.dusartFar_shift_geometry <;> assumption

example {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x) :
    let s := exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))
    let t := 1 - 3 * s
    exp (-(4 / 5 : ℝ) * sqrt (Real.log (x * t) / 6)) / 2 ≤ s / t ∧
      s / t ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log (x * t) / 6)) := by
  apply PrimeFactorUnimodality.dusartFar_left_step_window <;> assumption

example {b : ℝ} (hb : 4705 ≤ b) :
    exp (-(4 / 5 : ℝ) * sqrt (b / 6)) ≤ exp (-(4 / 5 : ℝ) * sqrt ((b - 1) / 6)) ∧
      exp (-(4 / 5 : ℝ) * sqrt ((b - 1) / 6)) ≤
        2 * exp (-(4 / 5 : ℝ) * sqrt (b / 6)) :=
  dusartFar_step_shift_le (by linarith) (by linarith) (by linarith)

end PrimeFactorUnimodality.Tests
