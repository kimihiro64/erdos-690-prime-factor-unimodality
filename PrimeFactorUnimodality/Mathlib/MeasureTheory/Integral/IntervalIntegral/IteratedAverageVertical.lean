/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.RotationError
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageScaling
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageStability

/-! # Stable vertical perturbations of averaged divided powers

Separate the common real amplitude from the changing unit phase and
reciprocal exponent. Pointwise errors pass through the averages without
inverse-step amplification, at every natural smoothing order.
-/

namespace Complex

/-- Equal real parts give a common amplitude and an explicit phase/reciprocal error. -/
theorem norm_cpow_div_sub_le_of_re_eq {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (he : z.re = w.re) {L : ℝ} (hL : 0 < L) (hz : L ≤ ‖z‖) (hw : L ≤ ‖w‖) :
    ‖(x : ℂ) ^ z / z - (x : ℂ) ^ w / w‖ ≤
      Real.exp (z.re * Real.log x) *
        (‖z - w‖ / L ^ 2 + |Real.log x| * |z.im - w.im| / L) := by
  rw [ofReal_cpow_eq_exp_mul_phase hx z, ofReal_cpow_eq_exp_mul_phase hx w, ← he]
  have hf : (Real.exp (z.re * Real.log x) : ℂ) * exp (I * ↑(Real.log x * z.im)) / z -
      (Real.exp (z.re * Real.log x) : ℂ) * exp (I * ↑(Real.log x * w.im)) / w =
      (Real.exp (z.re * Real.log x) : ℂ) *
        (exp (I * ↑(Real.log x * z.im)) / z - exp (I * ↑(Real.log x * w.im)) / w) := by ring
  rw [hf, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [← mul_sub, abs_mul] using
    norm_rotation_div_sub_le (Real.log x * z.im) (Real.log x * w.im) hL hz hw

end Complex

namespace intervalIntegral

open Complex Set

/-- A pointwise denominator lower bound controls an averaged divided power. -/
theorem norm_iteratedBoxAverageComplex_cpow_div_le_of_norm_ge {h L : ℝ} (hh : 0 < h)
    {z : ℂ} (hβ : 0 ≤ z.re) (hL : 0 < L) (hz : L ≤ ‖z‖) (n : ℕ) :
    ‖iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) 1‖ ≤
      Real.exp (z.re * Real.log (1 + n * h)) / L := by
  apply norm_iteratedBoxAverageComplex_le_on_Ici hh
    ((continuousOn_ofReal_cpow_Ici zero_lt_one z).div_const z) le_rfl n
  intro t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht.1
  have hl : Real.log t ≤ Real.log (1 + n * h) := Real.log_le_log ht0 ht.2
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos ht0, Real.rpow_def_of_pos ht0,
    mul_comm (Real.log t)]
  exact (div_le_div_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hβ)) (norm_nonneg z)).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hL hz)

/-- Vertical perturbation is stable uniformly over the whole averaging support. -/
theorem norm_iteratedBoxAverageComplex_cpow_div_sub_le {h L : ℝ} (hh : 0 < h)
    {z w : ℂ} (he : z.re = w.re) (hβ : 0 ≤ z.re)
    (hL : 0 < L) (hz : L ≤ ‖z‖) (hw : L ≤ ‖w‖) (n : ℕ) :
    ‖iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) 1 -
      iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ w / w) 1‖ ≤
      Real.exp (z.re * Real.log (1 + n * h)) *
        (‖z - w‖ / L ^ 2 + Real.log (1 + n * h) * |z.im - w.im| / L) := by
  apply norm_iteratedBoxAverageComplex_sub_le_on_Ici hh
    ((continuousOn_ofReal_cpow_Ici zero_lt_one z).div_const z)
    ((continuousOn_ofReal_cpow_Ici zero_lt_one w).div_const w) le_rfl n
  intro t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht.1
  have hl := Real.log_le_log ht0 ht.2
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht.1
  apply (norm_cpow_div_sub_le_of_re_eq ht0 he hL hz hw).trans
  rw [abs_of_nonneg (Real.log_nonneg ht.1)]
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hβ)
  · exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hl (abs_nonneg _)) hL.le)
  · positivity
  · exact (Real.exp_pos _).le

end intervalIntegral
