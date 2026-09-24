/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Cartesian evaluation of the principal logarithm in the right half-plane

Positive real part fixes the arctangent branch. The real coordinate uses
the logarithm of the squared norm, avoiding an intermediate square root.
Both coordinates are expressed using real functions of rational expressions.
-/

namespace Complex

/-- Positive real part fixes the principal argument to the ordinary arctangent branch. -/
theorem arg_eq_arctan_im_div_re_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    arg z = Real.arctan (z.im / z.re) := by
  have h := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  rw [← tan_arg]
  exact (Real.arctan_tan h.1 h.2).symm

/-- At positive height, evaluate arctangent at the reciprocal ratio rather than a huge argument. -/
theorem arg_eq_pi_div_two_sub_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) (hi : 0 < z.im) :
    arg z = Real.pi / 2 - Real.arctan (z.re / z.im) := by
  rw [arg_eq_arctan_im_div_re_of_re_pos hz]
  simpa only [inv_div] using Real.arctan_inv_of_pos (div_pos hz hi)

/-- The reciprocal-ratio evaluation keeps the correct branch at negative height too. -/
theorem arg_eq_neg_pi_div_two_sub_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) (hi : z.im < 0) :
    arg z = -(Real.pi / 2) - Real.arctan (z.re / z.im) := by
  rw [arg_eq_arctan_im_div_re_of_re_pos hz]
  simpa only [inv_div] using Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hz hi)

/-- The real logarithm coordinate can be evaluated without a square root. -/
theorem log_re_eq_half_log_normSq (z : ℂ) :
    (log z).re = Real.log (z.re ^ 2 + z.im ^ 2) / 2 := by
  have hs : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    ring
  rw [log_re, hs, Real.log_pow]
  ring

/-- Full principal complex logarithm using only real logarithm and arctangent. -/
theorem log_eq_cartesian_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    log z = ((Real.log (z.re ^ 2 + z.im ^ 2) / 2 : ℝ) : ℂ) +
      (Real.arctan (z.im / z.re) : ℂ) * I := by
  apply Complex.ext
  · simpa using log_re_eq_half_log_normSq z
  · simpa only [log_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, zero_add, add_zero] using arg_eq_arctan_im_div_re_of_re_pos hz

/-- Independent real-function enclosures give a complete complex logarithmic enclosure. -/
theorem norm_log_sub_cartesian_le {z : ℂ} (hz : 0 < z.re) {a b ε δ : ℝ}
    (ha : |Real.log (z.re ^ 2 + z.im ^ 2) - a| ≤ ε)
    (hb : |Real.arctan (z.im / z.re) - b| ≤ δ) :
    ‖log z - ((a / 2 : ℝ) : ℂ) - (b : ℂ) * I‖ ≤ ε / 2 + δ := by
  rw [log_eq_cartesian_of_re_pos hz]
  calc
    _ = ‖(((Real.log (z.re ^ 2 + z.im ^ 2) - a) / 2 : ℝ) : ℂ) +
        ((Real.arctan (z.im / z.re) - b : ℝ) : ℂ) * I‖ := by
      congr 1
      push_cast
      ring
    _ ≤ ‖(((Real.log (z.re ^ 2 + z.im ^ 2) - a) / 2 : ℝ) : ℂ)‖ +
        ‖((Real.arctan (z.im / z.re) - b : ℝ) : ℂ) * I‖ := norm_add_le _ _
    _ = |Real.log (z.re ^ 2 + z.im ^ 2) - a| / 2 +
        |Real.arctan (z.im / z.re) - b| := by
      simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right ha (by norm_num)) hb

end Complex
