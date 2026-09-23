import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleShift

/-! # Regression statements for the middle-range Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {x : ℝ} (hx : 1 < x) (hb : 85 ≤ Real.log x) :
    let s := (2 / 25 : ℝ) / Real.log x ^ 2
    let t := 1 - 3 * s
    (99 / 100 : ℝ) ≤ t ∧ t ≤ 1 ∧ 1 < x * t ∧
      Real.log x - 1 ≤ Real.log (x * t) ∧ Real.log (x * t) ≤ Real.log x := by
  apply PrimeFactorUnimodality.dusartMiddle_shift_geometry <;> assumption

example {x : ℝ} (hx : 1 < x) (hb : 85 ≤ Real.log x) :
    let s := (2 / 25 : ℝ) / Real.log x ^ 2
    let t := 1 - 3 * s
    (3 / 40 : ℝ) / Real.log (x * t) ^ 2 ≤ s / t ∧
      s / t ≤ (17 / 200 : ℝ) / Real.log (x * t) ^ 2 := by
  apply PrimeFactorUnimodality.dusartMiddle_left_step_window <;> assumption

end PrimeFactorUnimodality.Tests
