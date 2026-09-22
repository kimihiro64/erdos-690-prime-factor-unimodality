/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Bounds

/-! # Summing pole-subtracted finite Laplace transforms

An inverse-square norm majorant controls the remainder over any locally
finite family in a left half-plane. Multiplicities may be represented by
repeated values in the index family. No zero enumeration or hypothesis
about lying on a single vertical line is required.

The far-point comparison follows the triangle-inequality argument in
`Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq`,
from the Apache-2.0 `kimihiro64/PrimeNumberTheoremAnd` repository at
`f6147e7572ab3abe5428101bc0b13627bcb005df`. The explicit Laplace majorant
and generic indexed statement here use only Mathlib.
-/

namespace Complex

noncomputable section

open Set Filter

private theorem inv_norm_sub_le {s ρ : ℂ} (hfar : 2 * ‖s‖ < ‖ρ‖) :
    ‖s - ρ‖⁻¹ ≤ 2 * ‖ρ‖⁻¹ := by
  have htri : ‖ρ‖ ≤ ‖s‖ + ‖s - ρ‖ := by
    have ht := norm_add_le s (ρ - s)
    simpa only [add_sub_cancel, norm_sub_rev] using ht
  have hρpos : 0 < ‖ρ‖ := (by positivity : 0 ≤ 2 * ‖s‖).trans_lt hfar
  have hlow : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by linarith
  have hi := one_div_le_one_div_of_le (half_pos hρpos) hlow
  have hinv : ‖s - ρ‖⁻¹ ≤ (‖ρ‖ / 2)⁻¹ := by simpa only [one_div] using hi
  have hhalf : (‖ρ‖ / 2)⁻¹ = 2 * ‖ρ‖⁻¹ := by field_simp
  simpa only [hhalf] using hinv

/-- Translating a locally finite inverse-square family preserves inverse-square summability. -/
theorem summable_norm_sub_inv_sq {ι : Type*} (a : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hsum : Summable (fun i => ‖a i‖⁻¹ ^ 2)) (s : ℂ) :
    Summable (fun i => ‖s - a i‖⁻¹ ^ 2) := by
  have hmajor := hsum.mul_left 4
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [(hfinite (2 * ‖s‖)).eventually_cofinite_notMem] with i hi
  have hfar : 2 * ‖s‖ < ‖a i‖ := lt_of_not_ge hi
  have hinv := inv_norm_sub_le hfar
  have hsq : (‖s - a i‖⁻¹) ^ 2 ≤ (2 * ‖a i‖⁻¹) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hinv
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖s - a i‖⁻¹))]
  simpa only [mul_pow,
    show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq

/-- Far from the evaluation point, the remainder has an explicit inverse-square majorant. -/
theorem norm_finiteLaplace_sub_pole_le_inv_sq {f g h : ℝ → ℂ} {d M B : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M)
    {s ρ : ℂ} (hρ : ρ.re ≤ B) (hfar : 2 * ‖s‖ < ‖ρ‖) :
    ‖finiteLaplace f d (s - ρ) - f 0 / (s - ρ)‖ ≤
      (4 * M * d * Real.exp (max 0 (B - s.re) * d)) * ‖ρ‖⁻¹ ^ 2 := by
  have hw : s - ρ ≠ 0 := by
    intro heq
    have heq' := sub_eq_zero.mp heq
    rw [heq'] at hfar
    linarith [norm_nonneg ρ]
  have hmax : max 0 (-(s - ρ).re) ≤ max 0 (B - s.re) := by
    apply max_le_max_left
    simp only [sub_re]
    linarith
  let C : ℝ := M * d * Real.exp (max 0 (B - s.re) * d)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnum : M * d * Real.exp (max 0 (-(s - ρ).re) * d) ≤ C := by
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hmax hd)) (mul_nonneg hM hd)
  have hinv := inv_norm_sub_le hfar
  have hinv₂ : (‖s - ρ‖⁻¹) ^ 2 ≤ (2 * ‖ρ‖⁻¹) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hinv
  calc
    _ ≤ M * d * Real.exp (max 0 (-(s - ρ).re) * d) / ‖s - ρ‖ ^ 2 :=
      norm_finiteLaplace_sub_pole_le_exp hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hw
    _ ≤ C / ‖s - ρ‖ ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = C * (‖s - ρ‖⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ C * (2 * ‖ρ‖⁻¹) ^ 2 := mul_le_mul_of_nonneg_left hinv₂ hC
    _ = _ := by dsimp [C]; ring

/-- Absolute summability of the remainders over a locally finite inverse-square family. -/
theorem summable_finiteLaplace_sub_pole {ι : Type*} (a : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hsum : Summable (fun i => ‖a i‖⁻¹ ^ 2)) {B : ℝ} (ha : ∀ i, (a i).re ≤ B)
    {f g h : ℝ → ℂ} {d M : ℝ} (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) (s : ℂ) :
    Summable (fun i => finiteLaplace f d (s - a i) - f 0 / (s - a i)) := by
  have hmajor := hsum.mul_left (4 * M * d * Real.exp (max 0 (B - s.re) * d))
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [(hfinite (2 * ‖s‖)).eventually_cofinite_notMem] with i hi
  have hfar : 2 * ‖s‖ < ‖a i‖ := lt_of_not_ge hi
  exact norm_finiteLaplace_sub_pole_le_inv_sq hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (ha i) hfar

end

end Complex
