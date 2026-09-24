/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Gamma norms on half-integer vertical lines

Reflection gives the exact norm on the line with real part one half.
Recurrence then gives a polynomial majorant on every nonnegative integer
translate, after removing exponential decay. The signed-height estimate
is uniform, including zero and negative heights.
-/

open scoped ComplexConjugate

namespace Complex

/-- The exact squared Gamma norm on the central half-integer line. -/
theorem norm_Gamma_half_add_mul_I_sq (t : ℝ) :
    ‖Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hc : 1 - ((1 / 2 : ℂ) + (t : ℂ) * I) =
      conj ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext
    · norm_num
    · simp
  have hs : sin (Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) =
      (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * I by push_cast; ring]
    rw [sin_add_mul_I, sin_pi_div_two, cos_pi_div_two]
    simp
  have h := congrArg norm (Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + (t : ℂ) * I))
  rw [hc, Gamma_conj, norm_mul, norm_conj, hs, norm_div] at h
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos (Real.cosh_pos _)] at h
  simpa only [pow_two] using h

/-- Removing exponential decay gives a uniform bound at every signed height. -/
theorem norm_Gamma_half_add_mul_I_mul_exp_le (t : ℝ) :
    ‖Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ * Real.exp (Real.pi * t / 2) ≤
      Real.sqrt (2 * Real.pi) := by
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (Real.sqrt_nonneg _)).mp
  have he : Real.exp (Real.pi * t / 2) ^ 2 = Real.exp (Real.pi * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, norm_Gamma_half_add_mul_I_sq, he,
    Real.sq_sqrt (by positivity), div_mul_eq_mul_div]
  apply (div_le_iff₀ (Real.cosh_pos _)).mpr
  have hcosh : Real.exp (Real.pi * t) ≤ 2 * Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * t))]
  nlinarith [Real.pi_pos]

/-- Recurrence expresses each translated norm as the base norm times a finite product. -/
theorem norm_Gamma_nat_add_half (m : ℕ) (t : ℝ) :
    ‖Gamma ((m : ℂ) + 1 / 2 + (t : ℂ) * I)‖ =
      ‖Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
        ∏ j ∈ Finset.range m, ‖(j : ℂ) + 1 / 2 + (t : ℂ) * I‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hz : (m : ℂ) + 1 / 2 + (t : ℂ) * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have h := Gamma_add_one ((m : ℂ) + 1 / 2 + (t : ℂ) * I) hz
    have he : ((m + 1 : ℕ) : ℂ) + 1 / 2 + (t : ℂ) * I =
        ((m : ℂ) + 1 / 2 + (t : ℂ) * I) + 1 := by push_cast; ring
    rw [he, h, norm_mul, ih, Finset.prod_range_succ]
    ring

/-- Each recurrence factor is bounded by the largest real shift plus absolute height. -/
theorem norm_Gamma_nat_add_half_mul_exp_le (m : ℕ) (t : ℝ) :
    ‖Gamma ((m : ℂ) + 1 / 2 + (t : ℂ) * I)‖ * Real.exp (Real.pi * t / 2) ≤
      Real.sqrt (2 * Real.pi) * (|t| + (m : ℝ) - 1 / 2) ^ m := by
  have hp : (∏ j ∈ Finset.range m, ‖(j : ℂ) + 1 / 2 + (t : ℂ) * I‖) ≤
      (|t| + (m : ℝ) - 1 / 2) ^ m := by
    calc
      _ ≤ ∏ _j ∈ Finset.range m, (|t| + (m : ℝ) - 1 / 2) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j hj
        have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hj
        have htriangle := norm_add_le (((j : ℝ) + 1 / 2 : ℝ) : ℂ) ((t : ℂ) * I)
        have hnonneg : (0 : ℝ) ≤ j + 1 / 2 := by positivity
        simp only [norm_mul, norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hnonneg] at htriangle
        push_cast at htriangle
        linarith
      _ = _ := by simp
  rw [norm_Gamma_nat_add_half]
  calc
    _ = (‖Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ * Real.exp (Real.pi * t / 2)) *
        (∏ j ∈ Finset.range m, ‖(j : ℂ) + 1 / 2 + (t : ℂ) * I‖) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) *
        (∏ j ∈ Finset.range m, ‖(j : ℂ) + 1 / 2 + (t : ℂ) * I‖) :=
      mul_le_mul_of_nonneg_right (norm_Gamma_half_add_mul_I_mul_exp_le t)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)

/-- The odd-integer parametrization used by Gaussian-windowed Gamma error estimates. -/
theorem norm_Gamma_odd_half_mul_exp_le (m : ℕ) (u : ℝ) :
    ‖Gamma (((2 * (m : ℝ) + 1 : ℝ) : ℂ) / 2 + ((u / 2 : ℝ) : ℂ) * I)‖ *
        Real.exp (Real.pi * u / 4) ≤
      Real.sqrt (2 * Real.pi) * (|u| + 2 * (m : ℝ) - 1) ^ m / 2 ^ m := by
  have h := norm_Gamma_nat_add_half_mul_exp_le m (u / 2)
  have hp : |u / 2| + (m : ℝ) - 1 / 2 = (|u| + 2 * (m : ℝ) - 1) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [hp, div_pow] at h
  have hz : (((2 * (m : ℝ) + 1 : ℝ) : ℂ) / 2 + ((u / 2 : ℝ) : ℂ) * I) =
      (m : ℂ) + 1 / 2 + ((u / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [hz, show Real.pi * u / 4 = Real.pi * (u / 2) / 2 by ring]
  simpa only [mul_div_assoc] using h

end Complex
