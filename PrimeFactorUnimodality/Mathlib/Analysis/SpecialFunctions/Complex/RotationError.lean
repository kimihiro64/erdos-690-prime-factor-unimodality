/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Ring

/-! # Exact polar rescaling and error propagation under complex rotation

The real exponential amplitude separates from the unit rotation exactly.
Changing the rotation angle and the approximated complex value incurs
independent absolute errors, with no exponentially small scale factor.
-/

namespace Complex

/-- Separate the positive amplitude and the exact combined argument of a product with an exponential. -/
theorem mul_exp_eq_norm_exp_re_mul_rotation (p w : ℂ) :
    p * exp w = ((‖p‖ * Real.exp w.re : ℝ) : ℂ) * exp (I * (arg p + w.im)) := by
  have hw : exp w = (Real.exp w.re : ℂ) * exp (I * w.im) := by
    rw [ofReal_exp, ← exp_add]
    congr 1
    rw [mul_comm I, re_add_im]
  rw [hw, ofReal_mul, mul_add, exp_add]
  have hp := norm_mul_exp_arg_mul_I p
  rw [mul_comm (arg p : ℂ) I] at hp
  conv_lhs => rw [← hp]
  ring

/-- Unit rotations are Lipschitz with constant one in their real angle. -/
theorem norm_exp_I_mul_ofReal_sub_le (a b : ℝ) :
    ‖exp (I * a) - exp (I * b)‖ ≤ |a - b| := by
  have he : exp (I * a) - exp (I * b) =
      exp (I * b) * (exp (I * (a - b)) - 1) := by
    rw [mul_sub, ← exp_add]
    congr 1
    · congr 1
      ring
    · simp
  rw [he, norm_mul]
  simpa [norm_exp, mul_re, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- Rotation and value errors propagate independently, using the approximate value's norm. -/
theorem norm_rotated_sub_rotated_le (a b : ℝ) (z w : ℂ) :
    ‖exp (I * a) * z - exp (I * b) * w‖ ≤ ‖z - w‖ + ‖w‖ * |a - b| := by
  have he : exp (I * a) * z - exp (I * b) * w =
      exp (I * a) * (z - w) + (exp (I * a) - exp (I * b)) * w := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have hn : ‖exp (I * a)‖ = 1 := by simp [norm_exp, mul_re]
  rw [hn, one_mul]
  exact add_le_add le_rfl (by
    rw [mul_comm ‖w‖ |a - b|]
    exact mul_le_mul_of_nonneg_right (norm_exp_I_mul_ofReal_sub_le a b) (norm_nonneg w))

/-- The real part satisfies the same absolute error bound as the full rotated value. -/
theorem abs_re_rotated_sub_le (a b : ℝ) (z w : ℂ) :
    |(exp (I * a) * z).re - (exp (I * b) * w).re| ≤ ‖z - w‖ + ‖w‖ * |a - b| := by
  calc
    _ = |(exp (I * a) * z - exp (I * b) * w).re| := by rw [sub_re]
    _ ≤ ‖exp (I * a) * z - exp (I * b) * w‖ := abs_re_le_norm _
    _ ≤ _ := norm_rotated_sub_rotated_le a b z w

end Complex
