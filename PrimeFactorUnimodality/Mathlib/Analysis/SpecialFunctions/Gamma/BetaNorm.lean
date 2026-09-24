/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Bounds from the Beta integral

Taking absolute values inside the Beta integral removes both imaginary
parts. The resulting real Beta value bounds ratios of Gamma norms on
vertical lines in the open right half-plane.
-/

open MeasureTheory Set

namespace Complex

/-- The norm of the complex Beta integral is bounded by its real-parameter value. -/
theorem norm_betaIntegral_le {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖betaIntegral u v‖ ≤ Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) := by
  let f : ℝ → ℝ := fun x => x ^ (u.re - 1) * (1 - x) ^ (v.re - 1)
  have hf : (∫ x in (0 : ℝ)..1, f x) =
      Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    calc
      _ = betaIntegral (u.re : ℂ) (v.re : ℂ) := by
        unfold betaIntegral
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro x hx
        simp only [f, ofReal_mul, ofReal_cpow hx.1.le,
          ofReal_cpow (sub_pos.mpr hx.2).le, ofReal_sub, ofReal_one]
      _ = _ := by
        rw [betaIntegral_eq_Gamma_mul_div _ _ (by simpa) (by simpa)]
        simp only [ofReal_div, ofReal_mul, ← ofReal_add, Gamma_ofReal]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1,
        ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = ∫ x in (0 : ℝ)..1, f x := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro x hx
      dsimp only
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1,
        ← ofReal_one, ← ofReal_sub, norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
      simp only [f, sub_re, ofReal_re]
    _ = _ := hf

/-- A real positive shift bounds the ratio of Gamma norms independently of height. -/
theorem norm_Gamma_div_norm_Gamma_add_real_le {s : ℂ} (hs : 0 < s.re)
    {a : ℝ} (ha : 0 < a) :
    ‖Gamma s‖ / ‖Gamma (s + (a : ℂ))‖ ≤ Real.Gamma s.re / Real.Gamma (s.re + a) := by
  have h := norm_betaIntegral_le hs (show 0 < (a : ℂ).re from ha)
  rw [betaIntegral_eq_Gamma_mul_div _ _ hs ha, norm_div, norm_mul, Gamma_ofReal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos ha)] at h
  simp only [ofReal_re] at h
  rw [mul_div_right_comm, mul_div_right_comm] at h
  exact (mul_le_mul_iff_of_pos_right (Real.Gamma_pos_of_pos ha)).mp h

end Complex
