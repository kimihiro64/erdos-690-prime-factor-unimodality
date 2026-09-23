/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Elementary lower bounds for logarithms of multiples of pi

Combine the existing bounds for log two and log five with a rational
lower bound for pi and the elementary logarithm inequality.
-/

namespace Real

/-- A rational lower bound for the logarithm of four pi. -/
theorem log_four_mul_pi_gt_5061_div_2000 : (5061 / 2000 : ℝ) < Real.log (4 * π) := by
  have hr := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 625 / 628)
  rw [show (625 / 628 : ℝ) = (628 / 625)⁻¹ by norm_num, log_inv] at hr
  have hl : Real.log (314 / 25 : ℝ) =
      2 * Real.log 5 - Real.log 2 + Real.log (628 / 625) := by
    rw [show (314 / 25 : ℝ) = (5 ^ 2 / 2) * (628 / 625) by norm_num,
      log_mul (by positivity) (by positivity), log_div (by positivity) (by positivity), log_pow]
    norm_num
  have hp : (314 / 25 : ℝ) < 4 * π := by linarith [pi_gt_d20]
  have hb := Real.log_lt_log (by norm_num : (0 : ℝ) < 314 / 25) hp
  rw [hl] at hb
  linarith [log_five_gt_d9, log_two_lt_d9]

/-- A rational lower bound for the logarithm of two pi. -/
theorem log_two_mul_pi_gt_1837_div_1000 : (1837 / 1000 : ℝ) < Real.log (2 * π) := by
  have hl : Real.log (4 * π) = Real.log 2 + Real.log (2 * π) := by
    rw [show (4 : ℝ) * π = 2 * (2 * π) by ring, log_mul (by positivity) (by positivity)]
  linarith [log_four_mul_pi_gt_5061_div_2000, log_two_lt_d9]

/-- A coarse lower bound for log pi, obtained from the same existing logarithm estimates. -/
theorem log_pi_gt_57_div_50 : (57 / 50 : ℝ) < Real.log π := by
  have he : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [log_mul (by norm_num : (4 : ℝ) ≠ 0) pi_pos.ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  linarith [log_four_mul_pi_gt_5061_div_2000, log_two_lt_d9]

end Real
