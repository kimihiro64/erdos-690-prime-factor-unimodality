import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogHeightBounds

/-! # Exact interfaces and endpoint cases for the proved Turing counting budget -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Set

example {z : ℂ} (hy : 0 < z.im) (hx : 0 ≤ z.re) :
    Real.pi / 2 - z.re / z.im ≤ arg z := pi_div_two_sub_re_div_im_le_arg hy hx

example : Real.pi / 2 ≤ arg I := by
  simpa using pi_div_two_sub_re_div_im_le_arg (z := I) (by norm_num) (by norm_num)

example : Real.pi / 2 - 1 / 2 ≤ arg ((1 : ℂ) + 2 * I) := by
  convert pi_div_two_sub_re_div_im_le_arg (z := (1 : ℂ) + 2 * I)
    (by norm_num) (by norm_num) using 1 <;> norm_num

example {z : ℂ} (hy : 0 < z.im) :
    z.im * (Real.log ‖z‖ - Real.log z.im) ≤ z.re ^ 2 / (2 * z.im) := by
  exact Complex.im_mul_log_norm_sub_log_im_le hy

example {z : ℂ} (hy : 0 < z.im) (hx : z.re ≤ 0) :
    arg z ≤ Real.pi / 2 - z.re / z.im := by
  exact Complex.arg_le_pi_div_two_sub_re_div_im hy hx

example (x : ℝ) : Real.log ‖(x : ℂ) + I‖ ≤ x ^ 2 / 2 := by
  simpa using im_mul_log_norm_sub_log_im_le (z := (x : ℂ) + I) (by simp)

example : arg I ≤ Real.pi / 2 := by
  have h := arg_le_pi_div_two_sub_re_div_im (z := I) (by norm_num) (by norm_num)
  simpa only [I_re, zero_div, sub_zero] using h

example : arg ((-1 : ℂ) + 2 * I) ≤ Real.pi / 2 + 1 / 2 := by
  convert arg_le_pi_div_two_sub_re_div_im (z := (-1 : ℂ) + 2 * I)
    (by norm_num) (by norm_num) using 1
  norm_num

end

end PrimeFactorUnimodality.Tests
