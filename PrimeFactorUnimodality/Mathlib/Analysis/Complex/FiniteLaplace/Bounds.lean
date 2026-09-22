/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic

/-! # Explicit bounds for finite Laplace transforms

A uniform bound on the source gives an explicit exponential bound on every
vertical line, and a sharper inverse-real-part bound on the right half-plane.
After two integrations by parts these give a quadratic denominator for the
pole-subtracted transform. No unspecified asymptotic constant is used.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- The finite interval controls the transform even on vertical lines with negative real part. -/
theorem norm_finiteLaplace_le_exp {f : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M) (hf : ∀ t ∈ Icc 0 d, ‖f t‖ ≤ M) (s : ℂ) :
    ‖finiteLaplace f d s‖ ≤ M * d * Real.exp (max 0 (-s.re) * d) := by
  have hbound (t : ℝ) (ht : t ∈ uIoc 0 d) :
      ‖exp (-s * (t : ℂ)) * f t‖ ≤ M * Real.exp (max 0 (-s.re) * d) := by
    rw [uIoc_of_le hd] at ht
    have harg : -s.re * t ≤ max 0 (-s.re) * d :=
      (mul_le_mul_of_nonneg_right (le_max_right 0 (-s.re)) ht.1.le).trans
        (mul_le_mul_of_nonneg_left ht.2 (le_max_left 0 (-s.re)))
    rw [norm_mul, norm_exp]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
    rw [hre, mul_comm]
    exact mul_le_mul (hf t ⟨ht.1.le, ht.2⟩) (Real.exp_le_exp.mpr harg)
      (Real.exp_nonneg _) hM
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [finiteLaplace, sub_zero, abs_of_nonneg hd, mul_right_comm] using h

/-- A uniform source bound gives an explicit inverse-real-part bound on the right half-plane. -/
theorem norm_finiteLaplace_le_div_re {f : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M) (hf : ∀ t ∈ Icc 0 d, ‖f t‖ ≤ M)
    {s : ℂ} (hs : 0 < s.re) : ‖finiteLaplace f d s‖ ≤ M / s.re := by
  have hbound : ∀ᵐ t : ℝ, t ∈ Ioc 0 d →
      ‖exp (-s * (t : ℂ)) * f t‖ ≤ M * Real.exp (-s.re * t) := by
    filter_upwards with t ht
    rw [norm_mul, norm_exp]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
    rw [hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf t ⟨ht.1.le, ht.2⟩) (Real.exp_nonneg _)
  have hi : IntervalIntegrable (fun t : ℝ => M * Real.exp (-s.re * t)) volume 0 d :=
    (by fun_prop : Continuous (fun t : ℝ => M * Real.exp (-s.re * t))).intervalIntegrable 0 d
  have h := intervalIntegral.norm_integral_le_of_norm_le hd hbound hi
  have heq : (∫ t in (0 : ℝ)..d, Real.exp (-s.re * t)) =
      (1 - Real.exp (-s.re * d)) / s.re := by
    rw [intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr hs.ne'),
      integral_exp]
    simp only [mul_zero, Real.exp_zero, smul_eq_mul, inv_neg]
    ring
  rw [intervalIntegral.integral_const_mul, heq] at h
  change ‖finiteLaplace f d s‖ ≤ _ at h
  apply h.trans
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hs]
  nlinarith [mul_nonneg hM (Real.exp_nonneg (-s.re * d))]

/-- Quantitative pole-subtracted bound on an arbitrary vertical line. -/
theorem norm_finiteLaplace_sub_pole_le_exp {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) {s : ℂ} (hs : s ≠ 0) :
    ‖finiteLaplace f d s - f 0 / s‖ ≤
      M * d * Real.exp (max 0 (-s.re) * d) / ‖s‖ ^ 2 := by
  rw [finiteLaplace_eq_pole_add hd hf hg hh hfg hgh hfd hg₀ hgd hs,
    add_sub_cancel_left, norm_div, norm_pow]
  exact div_le_div_of_nonneg_right (norm_finiteLaplace_le_exp hd hM hbound s)
    (sq_nonneg _)

/-- The sharper pole-subtracted bound in the right half-plane has its full explicit constant. -/
theorem norm_finiteLaplace_sub_pole_le_div_re {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖finiteLaplace f d s - f 0 / s‖ ≤ M / (s.re * ‖s‖ ^ 2) := by
  have hs₀ : s ≠ 0 := by intro heq; simp [heq] at hs
  rw [finiteLaplace_eq_pole_add hd hf hg hh hfg hgh hfd hg₀ hgd hs₀,
    add_sub_cancel_left, norm_div, norm_pow, ← div_div]
  exact div_le_div_of_nonneg_right (norm_finiteLaplace_le_div_re hd hM hbound hs)
    (sq_nonneg _)

end

end Complex
