/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.ThreeKernel

/-! # Uniform coefficient bounds for three rational kernels

The leading and constant coefficients are controlled uniformly when the
first scale lies between a positive lower bound and one, and the error
coefficient is bounded above. The two bounds retain their exact parameters.
-/

namespace Real

/-- Fixed parameter bounds imply both coefficients required by the three-kernel criterion. -/
theorem threeKernel_coefficients_of_uniform_bounds {g e E r₀ r δ κ : ℝ}
    (hg : 0 ≤ g) (he : 0 ≤ e) (heE : e ≤ E) (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r) (hr₁ : r ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (h₂ : κ * ((1 + 2 * δ) * g + (1 / δ + 1 / (δ + r₀)) * E) ≤ g * r₀ - E / r₀)
    (h₃ : κ * ((1 / δ + (1 + δ) / (δ + r₀) ^ 2) * g +
      (1 / δ ^ 3 + 1 / (δ + r₀) ^ 3) * E) ≤ g * r₀ - E / r₀) :
    0 ≤ (g * r - e / r) - κ * ((g * δ + e / δ) + (g * (r + δ) + e / (r + δ))) ∧
    0 ≤ (g * r - e / r) * δ ^ 2 * (r + δ) ^ 2 - κ * r ^ 2 *
      ((g * δ + e / δ) * (r + δ) ^ 2 + (g * (r + δ) + e / (r + δ)) * δ ^ 2) := by
  have hrpos := hr₀.trans_le hr
  have hE := he.trans heE
  have hb₀ := add_pos hδ hr₀
  have hb := add_pos hrpos hδ
  have hbb : δ + r₀ ≤ r + δ := by linarith
  have hbb₂ : (δ + r₀) ^ 2 ≤ (r + δ) ^ 2 := by nlinarith
  have hbb₃ : (δ + r₀) ^ 3 ≤ (r + δ) ^ 3 := pow_le_pow_left₀ hb₀.le hbb 3
  have hA : g * r₀ - E / r₀ ≤ g * r - e / r :=
    sub_le_sub (mul_le_mul_of_nonneg_left hr hg) (div_le_div₀ hE heE hr₀ hr)
  have hB : (g * δ + e / δ) + (g * (r + δ) + e / (r + δ)) ≤
      (1 + 2 * δ) * g + (1 / δ + 1 / (δ + r₀)) * E := by
    have hlin := mul_le_mul_of_nonneg_left hr₁ hg
    have hdiv₁ := div_le_div_of_nonneg_right heE hδ.le
    have hdiv₂ := div_le_div₀ hE heE hb₀ hbb
    simp only [add_mul, one_div_mul_eq_div] at *
    linarith
  let U := (1 / δ + (1 + δ) / (δ + r₀) ^ 2) * g +
    (1 / δ ^ 3 + 1 / (δ + r₀) ^ 3) * E
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hquot (x : ℝ) (hx : 0 < x) :
      (g * x + e / x) / x ^ 2 = g * x / x ^ 2 + e / x ^ 3 := by
    field_simp
  have hB₀ : (g * δ + e / δ) / δ ^ 2 ≤ g / δ + E / δ ^ 3 := by
    rw [hquot δ hδ]
    have heq : g * δ / δ ^ 2 = g / δ := by field_simp
    rw [heq]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right heE (show 0 ≤ δ ^ 3 by positivity))
  have hC₀ : (g * (r + δ) + e / (r + δ)) / (r + δ) ^ 2 ≤
      g * (1 + δ) / (δ + r₀) ^ 2 + E / (δ + r₀) ^ 3 := by
    rw [hquot (r + δ) hb]
    exact add_le_add
      (div_le_div₀ (mul_nonneg hg (by positivity))
        (mul_le_mul_of_nonneg_left (by linarith) hg) (sq_pos_of_pos hb₀) hbb₂)
      (div_le_div₀ hE heE (pow_pos hb₀ 3) hbb₃)
  have hsum : (g * δ + e / δ) / δ ^ 2 +
      (g * (r + δ) + e / (r + δ)) / (r + δ) ^ 2 ≤ U := by
    convert add_le_add hB₀ hC₀ using 1
    dsimp [U]
    ring
  have hr₂ : r ^ 2 ≤ 1 := by nlinarith
  have hzero : κ * r ^ 2 * ((g * δ + e / δ) / δ ^ 2 +
      (g * (r + δ) + e / (r + δ)) / (r + δ) ^ 2) ≤ g * r - e / r := by
    calc
      _ ≤ κ * r ^ 2 * U := mul_le_mul_of_nonneg_left hsum (mul_nonneg hκ (sq_nonneg _))
      _ ≤ κ * U := by nlinarith [mul_nonneg hκ hU]
      _ ≤ g * r₀ - E / r₀ := h₃
      _ ≤ _ := hA
  constructor
  · have h := (mul_le_mul_of_nonneg_left hB hκ).trans (h₂.trans hA)
    linarith
  · have h := mul_nonneg (sub_nonneg.mpr hzero) (mul_nonneg (sq_nonneg δ) (sq_nonneg (r + δ)))
    have heq : (g * r - e / r - κ * r ^ 2 *
        ((g * δ + e / δ) / δ ^ 2 + (g * (r + δ) + e / (r + δ)) / (r + δ) ^ 2)) *
        (δ ^ 2 * (r + δ) ^ 2) =
        (g * r - e / r) * δ ^ 2 * (r + δ) ^ 2 - κ * r ^ 2 *
          ((g * δ + e / δ) * (r + δ) ^ 2 + (g * (r + δ) + e / (r + δ)) * δ ^ 2) := by
      field_simp
    rwa [heq] at h

end Real
