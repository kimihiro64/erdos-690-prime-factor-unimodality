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

/-- Integer quarter turns reduce exactly to four powers of `I`, including negative turns. -/
theorem exp_int_quarter_turn (q : ℤ) :
    exp (I * (((q : ℝ) * Real.pi / 2 : ℝ) : ℂ)) = I ^ (q % 4) := by
  calc
    _ = exp ((q : ℂ) * ((Real.pi : ℂ) / 2 * I)) := by
      congr 1
      push_cast
      ring
    _ = I ^ q := by rw [exp_int_mul, exp_pi_div_two_mul_I]
    _ = I ^ (q % 4) := I_zpow_eq_zpow_mod q

/-- Separate the positive amplitude and combined argument of a product with an exponential. -/
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

/-- Denominators bounded away from zero have an explicit rotated reciprocal error. -/
theorem norm_rotation_div_sub_le (a b : ℝ) {z w : ℂ} {L : ℝ}
    (hL : 0 < L) (hz : L ≤ ‖z‖) (hw : L ≤ ‖w‖) :
    ‖exp (I * a) / z - exp (I * b) / w‖ ≤
      ‖z - w‖ / L ^ 2 + |a - b| / L := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hL.trans_le hz)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hL.trans_le hw)
  have hinv : ‖z⁻¹ - w⁻¹‖ ≤ ‖z - w‖ / L ^ 2 := by
    have he := dist_inv_inv₀ hz0 hw0
    simp only [dist_eq_norm] at he
    rw [he]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hL)
    simpa only [pow_two] using mul_le_mul hz hw hL.le (norm_nonneg z)
  have hw' : ‖w⁻¹‖ ≤ L⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hL hw
  simp only [div_eq_mul_inv]
  apply (norm_rotated_sub_rotated_le a b z⁻¹ w⁻¹).trans
  have he := add_le_add hinv (mul_le_mul_of_nonneg_right hw' (abs_nonneg (a - b)))
  simpa only [div_eq_mul_inv, mul_comm L⁻¹] using he

/-- A real rotated value changes its real part by an exact cosine factor under another rotation. -/
theorem re_rotated_eq_cos_mul_of_im_eq_zero (a b : ℝ) (z : ℂ)
    (hz : (exp (I * a) * z).im = 0) :
    (exp (I * b) * z).re = Real.cos (b - a) * (exp (I * a) * z).re := by
  have he : exp (I * b) * z = exp (I * (b - a)) * (exp (I * a) * z) := by
    rw [← mul_assoc, ← exp_add]
    congr 2
    ring
  rw [he, mul_re, hz, mul_zero, sub_zero]
  rw [mul_comm I, ← ofReal_sub, exp_ofReal_mul_I_re]

/-- A rotation of less than a quarter turn preserves the positive sign of a real value. -/
theorem re_rotated_pos_iff_of_im_eq_zero (a b : ℝ) (z : ℂ)
    (hz : (exp (I * a) * z).im = 0) (hab : |b - a| < Real.pi / 2) :
    0 < (exp (I * b) * z).re ↔ 0 < (exp (I * a) * z).re := by
  rw [re_rotated_eq_cos_mul_of_im_eq_zero a b z hz]
  exact mul_pos_iff_of_pos_left (Real.cos_pos_of_mem_Ioo (abs_lt.mp hab))

/-- A rotation of less than a quarter turn also preserves the negative sign of a real value. -/
theorem re_rotated_neg_iff_of_im_eq_zero (a b : ℝ) (z : ℂ)
    (hz : (exp (I * a) * z).im = 0) (hab : |b - a| < Real.pi / 2) :
    (exp (I * b) * z).re < 0 ↔ (exp (I * a) * z).re < 0 := by
  rw [re_rotated_eq_cos_mul_of_im_eq_zero a b z hz]
  have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp hab)
  constructor
  · intro h
    rcases mul_neg_iff.mp h with h | h
    · exact h.2
    · exact (not_lt_of_ge hc.le h.1).elim
  · intro h
    exact mul_neg_of_pos_of_neg hc h

end Complex
