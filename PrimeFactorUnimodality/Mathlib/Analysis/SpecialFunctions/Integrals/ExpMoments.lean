/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Exp.Cubic

/-! # Bounding exponential integrals by four moments

A cubic exponential majorant on a nonnegative interval controls a weighted
integral at every nonpositive transform argument in its domain. Keeping
the first four moments separately allows sharp, direction-aware numerical
bounds later without replacing the source by its supremum.
-/

namespace intervalIntegral

open MeasureTheory Set

/-- A single endpoint estimate bounds the weighted exponential integral by its four moments. -/
theorem integral_mul_exp_le_cubic_moments {f : ℝ → ℝ} {d z y C : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (hf₀ : ∀ u ∈ Icc 0 d, 0 ≤ f u)
    (hz : z ≤ 0) (hy : 0 < y) (hzy : -z * d ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + C * y ^ 3) :
    (∫ u in (0 : ℝ)..d, f u * Real.exp (-z * u)) ≤
      (∫ u in (0 : ℝ)..d, f u) - z * (∫ u in (0 : ℝ)..d, u * f u) +
        z ^ 2 / 2 * (∫ u in (0 : ℝ)..d, u ^ 2 * f u) -
        C * z ^ 3 * (∫ u in (0 : ℝ)..d, u ^ 3 * f u) := by
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  have hm (n : ℕ) : IntervalIntegrable (fun u => u ^ n * f u) volume 0 d :=
    ((continuous_id.pow n).continuousOn.mul hf').intervalIntegrable
  have h₀ : IntervalIntegrable f volume 0 d := hf'.intervalIntegrable
  have h₁ : IntervalIntegrable (fun u => z * (u * f u)) volume 0 d := by
    simpa only [pow_one] using (hm 1).const_mul z
  have h₂ := (hm 2).const_mul (z ^ 2 / 2)
  have h₃ := (hm 3).const_mul (C * z ^ 3)
  have hk : Continuous (fun u : ℝ => Real.exp (-z * u)) := by fun_prop
  have hi : IntervalIntegrable (fun u => f u * Real.exp (-z * u)) volume 0 d :=
    (hf'.mul hk.continuousOn).intervalIntegrable
  calc
    _ ≤ ∫ u in (0 : ℝ)..d,
        (f u - z * (u * f u) + z ^ 2 / 2 * (u ^ 2 * f u) - C * z ^ 3 * (u ^ 3 * f u)) := by
      apply integral_mono_on hd hi (((h₀.sub h₁).add h₂).sub h₃)
      intro u hu
      have h := mul_le_mul_of_nonneg_left
        (Real.exp_le_cubic_of_endpoint hy (mul_nonneg (neg_nonneg.mpr hz) hu.1)
          ((mul_le_mul_of_nonneg_left hu.2 (neg_nonneg.mpr hz)).trans hzy) hend) (hf₀ u hu)
      convert h using 1
      ring
    _ = _ := by
      rw [integral_sub ((h₀.sub h₁).add h₂) h₃, integral_add (h₀.sub h₁) h₂,
        integral_sub h₀ h₁]
      simp only [integral_const_mul]

end intervalIntegral
