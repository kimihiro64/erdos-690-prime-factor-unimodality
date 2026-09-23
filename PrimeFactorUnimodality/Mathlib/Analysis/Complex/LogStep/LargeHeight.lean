/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.Basic

/-! # Inverse-square decay of a logarithmic step

Applying `log t ≤ t - 1` to the ratio of squared distances retains quadratic
decay in the imaginary part, sufficient for absolute zero-sum comparison.
-/

namespace Complex

open MeasureTheory Set

private theorem log_sub_log_le_sq_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a ^ 2 - b ^ 2) / (2 * b ^ 2) := by
  have h := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb))
  rw [Real.log_div (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne'), Real.log_pow,
    Real.log_pow] at h
  apply (le_div_iff₀ (by positivity : 0 < 2 * b ^ 2)).mpr
  have hh := (le_div_iff₀ (sq_pos_of_pos hb)).mp
    (show 2 * (Real.log a - Real.log b) + 1 ≤ a ^ 2 / b ^ 2 by
      norm_num at h
      linarith)
  nlinarith

/-- A nonzero imaginary part bounds every step by twice its inverse square. -/
theorem logNormStep_le_inv_im_sq {w : ℂ} (hw : |w.re| ≤ 1 / 2) (hv : w.im ≠ 0)
    {x : ℝ} (hx : x ∈ Icc 0 1) : logNormStep w x ≤ 2 / w.im ^ 2 := by
  have hsq0 := norm_real_sub_sq w x
  have hsq1 := norm_real_sub_sq w (x + 1)
  have hvpos : 0 < w.im ^ 2 := sq_pos_of_ne_zero hv
  have hpos0 : 0 < ‖(x : ℂ) - w‖ := by nlinarith [norm_nonneg ((x : ℂ) - w)]
  have hpos1 : 0 < ‖((x + 1 : ℝ) : ℂ) - w‖ := by
    nlinarith [norm_nonneg (((x + 1 : ℝ) : ℂ) - w)]
  have hdiff : ‖((x + 1 : ℝ) : ℂ) - w‖ ^ 2 - ‖(x : ℂ) - w‖ ^ 2 ≤ 4 := by
    nlinarith [(abs_le.mp hw).1, hx.2]
  have hbound := log_sub_log_le_sq_ratio hpos1 hpos0
  unfold logNormStep
  apply hbound.trans
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * ‖(x : ℂ) - w‖ ^ 2) hvpos).mpr
  have hm := mul_le_mul_of_nonneg_right hdiff hvpos.le
  nlinarith [sq_nonneg (x - w.re)]

/-- Integrating the pointwise bound preserves the inverse-square height decay. -/
theorem logNormStepIntegral_le_inv_im_sq {w : ℂ} (hw : |w.re| ≤ 1 / 2)
    (hv : w.im ≠ 0) : logNormStepIntegral w ≤ 2 / w.im ^ 2 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_logNormStep w 0 1) intervalIntegrable_const
    (fun x hx => logNormStep_le_inv_im_sq hw hv hx)
  simpa only [logNormStepIntegral, intervalIntegral.integral_const, sub_zero,
    one_smul] using h

end Complex
