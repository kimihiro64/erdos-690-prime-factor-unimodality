/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Summability

/-! # Uniform bounds for entire paired Laplace contributions

Pairing `F(s-rho)` with `f(0)/rho` cancels the first-order tail while
preserving entire dependence on `s`. The explicit inverse-square bound
is uniform on a closed ball, not merely pointwise in `s`.
-/

namespace Complex

noncomputable section

open Set

/-- A paired contribution has a uniform inverse-square majorant on a parameter ball. -/
theorem norm_finiteLaplace_add_reciprocal_le_inv_sq
    {f g h : ℝ → ℂ} {d M B R : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M)
    {s ρ : ℂ} (hs : ‖s‖ ≤ R) (hρ : ρ.re ≤ B) (hfar : 2 * R < ‖ρ‖) :
    ‖finiteLaplace f d (s - ρ) + f 0 / ρ‖ ≤
      (4 * M * d * Real.exp (max 0 (B + R) * d) + 2 * ‖f 0‖ * R) * ‖ρ‖⁻¹ ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg s).trans hs
  have hρpos : 0 < ‖ρ‖ := (by positivity : 0 ≤ 2 * R).trans_lt hfar
  have hρ₀ : ρ ≠ 0 := norm_pos_iff.mp hρpos
  have htri : ‖ρ‖ ≤ ‖s‖ + ‖s - ρ‖ := by
    simpa only [add_sub_cancel, norm_sub_rev] using norm_add_le s (ρ - s)
  have hlow : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by linarith
  have hwpos : 0 < ‖s - ρ‖ := (half_pos hρpos).trans_le hlow
  have hw : s - ρ ≠ 0 := norm_pos_iff.mp hwpos
  have hinv : ‖s - ρ‖⁻¹ ≤ 2 * ‖ρ‖⁻¹ := by
    have hi := one_div_le_one_div_of_le (half_pos hρpos) hlow
    simpa [one_div, inv_div, div_eq_mul_inv] using hi
  have hr := norm_finiteLaplace_sub_pole_le_inv_sq hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hρ (by linarith : 2 * ‖s‖ < ‖ρ‖)
  have hreal : -s.re ≤ ‖s‖ := by simpa using re_le_norm (-s)
  have he : B - s.re ≤ B + R := by linarith
  have hr' : ‖finiteLaplace f d (s - ρ) - f 0 / (s - ρ)‖ ≤
      (4 * M * d * Real.exp (max 0 (B + R) * d)) * ‖ρ‖⁻¹ ^ 2 := hr.trans <|
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (max_le_max_left 0 he) hd)) (by positivity))
      (sq_nonneg _)
  have heq : finiteLaplace f d (s - ρ) + f 0 / ρ =
      (finiteLaplace f d (s - ρ) - f 0 / (s - ρ)) +
        f 0 * (s / ((s - ρ) * ρ)) := by
    field_simp
    ring
  have hc : ‖f 0 * (s / ((s - ρ) * ρ))‖ ≤ (2 * ‖f 0‖ * R) * ‖ρ‖⁻¹ ^ 2 := by
    rw [norm_mul, norm_div, norm_mul, div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv]
    calc
      _ ≤ ‖f 0‖ * (R * (2 * ‖ρ‖⁻¹) * ‖ρ‖⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hs hinv (inv_nonneg.mpr (norm_nonneg _)) hR)
            (inv_nonneg.mpr (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hr' hc).trans_eq (by ring))

end

end Complex
