/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Height-decaying logarithmic norm and argument bounds

The exact squared norm and `log x <= x-1` give a quadratic horizontal
error above the imaginary axis. The upper-left-quadrant argument bound
follows from `theta <= tan theta`, with all branch endpoints explicit.
Both quadrant argument estimates decay with the actual imaginary height.
-/

namespace Complex

/-- In the upper-right quadrant, the argument deficit is at most displacement over height. -/
theorem pi_div_two_sub_re_div_im_le_arg {z : ℂ} (hy : 0 < z.im) (hx : 0 ≤ z.re) :
    Real.pi / 2 - z.re / z.im ≤ arg z := by
  have hz : z ≠ 0 := by intro he; simp [he] at hy
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hlow : 0 ≤ Real.pi / 2 - arg z := by
    have := arg_le_pi_div_two_iff.mpr (Or.inl hx)
    linarith
  have hhigh : Real.pi / 2 - arg z < Real.pi / 2 := by
    have hn := arg_nonneg_iff.mpr hy.le
    have he : arg z ≠ 0 := by
      intro he
      have hm := (arg_eq_zero_iff.mp he).2
      linarith
    have hp := lt_of_le_of_ne hn (Ne.symm he)
    linarith
  have ht := Real.le_tan hlow hhigh
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
    sin_arg, cos_arg hz] at ht
  have he : (z.re / ‖z‖) / (z.im / ‖z‖) = z.re / z.im := by field_simp
  rw [he] at ht
  linarith

/-- The logarithmic norm correction decays quadratically in the horizontal displacement. -/
theorem im_mul_log_norm_sub_log_im_le {z : ℂ} (hy : 0 < z.im) :
    z.im * (Real.log ‖z‖ - Real.log z.im) ≤ z.re ^ 2 / (2 * z.im) := by
  have hn : 0 < ‖z‖ := hy.trans_le (im_le_norm z)
  have hl := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hn) (sq_pos_of_pos hy))
  calc
    _ = z.im / 2 * Real.log (‖z‖ ^ 2 / z.im ^ 2) := by
      rw [Real.log_div (ne_of_gt (sq_pos_of_pos hn)) (ne_of_gt (sq_pos_of_pos hy)),
        Real.log_pow, Real.log_pow]
      norm_num
      ring
    _ ≤ z.im / 2 * (‖z‖ ^ 2 / z.im ^ 2 - 1) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by
      rw [Complex.sq_norm, normSq_apply]
      field_simp
      ring

/-- In the upper-left quadrant, the excess argument is at most horizontal distance over height. -/
theorem arg_le_pi_div_two_sub_re_div_im {z : ℂ} (hy : 0 < z.im) (hx : z.re ≤ 0) :
    arg z ≤ Real.pi / 2 - z.re / z.im := by
  have hz : z ≠ 0 := by intro he; simp [he] at hy
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hlow : 0 ≤ arg z - Real.pi / 2 := by
    by_contra hn
    have ha : arg z < Real.pi / 2 := by linarith
    rcases arg_lt_pi_div_two_iff.mp ha with hr | hi | he
    · linarith
    · linarith
    · exact hz he
  have hhigh : arg z - Real.pi / 2 < Real.pi / 2 := by
    have := arg_lt_pi_iff.mpr (Or.inr hy.ne')
    linarith
  have ht := Real.le_tan hlow hhigh
  rw [Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two,
    Real.cos_sub_pi_div_two, sin_arg, cos_arg hz] at ht
  have he : -(z.re / ‖z‖) / (z.im / ‖z‖) = -z.re / z.im := by
    field_simp
  rw [he, neg_div] at ht
  linarith

end Complex
