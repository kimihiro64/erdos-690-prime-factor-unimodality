/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.RotationError

/-! # Stability and interpolation of weighted exponential sums

Coefficient and frequency errors are independent. A finite weighted frequency
mass also bounds variation between samples, without assuming distinct or
separated frequencies. Thus the same estimates retain repeated zero labels.
-/

namespace Complex

open Finset

variable {ι : Type*}

/-- A complex logarithmic error controls both amplitude and phase after exponentiation. -/
theorem norm_exp_sub_exp_le_of_norm_sub_le {z w : ℂ} {ε : ℝ} (hε : ‖z - w‖ ≤ ε) :
    ‖exp z - exp w‖ ≤ Real.exp w.re * (Real.exp ε - 1) := by
  have he : exp z - exp w = exp w * (exp (z - w) - 1) := by
    rw [mul_sub, ← exp_add, mul_one, add_sub_cancel]
  have hd : ‖exp (z - w) - 1‖ ≤ Real.exp ‖z - w‖ - 1 := by
    simpa using norm_exp_sub_sum_le_exp_norm_sub_sum (z - w) 1
  rw [he, norm_mul, norm_exp]
  exact mul_le_mul_of_nonneg_left
    (hd.trans (sub_le_sub_right (Real.exp_le_exp.mpr hε) 1)) (Real.exp_pos _).le

/-- A finite phase sum retains every coefficient and frequency perturbation. -/
theorem norm_expSum_sub_expSum_le (S : Finset ι) (w a : ι → ℂ)
    (f g : ι → ℝ) (u v : ℝ) :
    ‖(∑ i ∈ S, w i * exp (I * ((u * f i : ℝ) : ℂ))) -
      ∑ i ∈ S, a i * exp (I * ((v * g i : ℝ) : ℂ))‖ ≤
      ∑ i ∈ S, (‖w i - a i‖ + ‖a i‖ * |u * f i - v * g i|) := by
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  simpa only [mul_comm (w i), mul_comm (a i)] using
    norm_rotated_sub_rotated_le (u * f i) (v * g i) (w i) (a i)

/-- Enclosing frequencies gives a uniform error over the whole parameter window. -/
theorem norm_expSum_sub_expSum_le_of_enclosures (S : Finset ι) (w a : ι → ℂ)
    (f g ε δ : ι → ℝ) {v V : ℝ} (hv : |v| ≤ V)
    (hw : ∀ i ∈ S, ‖w i - a i‖ ≤ ε i)
    (hf : ∀ i ∈ S, |f i - g i| ≤ δ i) :
    ‖(∑ i ∈ S, w i * exp (I * ((v * f i : ℝ) : ℂ))) -
      ∑ i ∈ S, a i * exp (I * ((v * g i : ℝ) : ℂ))‖ ≤
      ∑ i ∈ S, (ε i + ‖a i‖ * (V * δ i)) := by
  apply (norm_expSum_sub_expSum_le S w a f g v v).trans
  apply sum_le_sum
  intro i hi
  apply add_le_add (hw i hi)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul hv (hf i hi) (abs_nonneg _) ((abs_nonneg v).trans hv)

/-- The first absolute frequency moment controls variation between any two samples. -/
theorem norm_expSum_sub_expSum_le_frequency_mass (S : Finset ι)
    (w : ι → ℂ) (f : ι → ℝ) (u v : ℝ) :
    ‖(∑ i ∈ S, w i * exp (I * ((u * f i : ℝ) : ℂ))) -
      ∑ i ∈ S, w i * exp (I * ((v * f i : ℝ) : ℂ))‖ ≤
      |u - v| * ∑ i ∈ S, ‖w i‖ * |f i| := by
  refine (norm_expSum_sub_expSum_le S w w f f u v).trans_eq ?_
  simp only [sub_self, norm_zero, zero_add, ← sub_mul, abs_mul, mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

/-- A checked sample and a distance bound enclose an entire neighboring interval. -/
theorem norm_expSum_le_of_sample (S : Finset ι) (w : ι → ℂ) (f : ι → ℝ)
    {u v d e : ℝ} {z : ℂ} (hd : |u - v| ≤ d)
    (hz : ‖(∑ i ∈ S, w i * exp (I * ((v * f i : ℝ) : ℂ))) - z‖ ≤ e) :
    ‖∑ i ∈ S, w i * exp (I * ((u * f i : ℝ) : ℂ))‖ ≤
      ‖z‖ + e + d * ∑ i ∈ S, ‖w i‖ * |f i| := by
  have hsample := (norm_le_norm_add_norm_sub'
    (∑ i ∈ S, w i * exp (I * ((v * f i : ℝ) : ℂ))) z).trans (add_le_add le_rfl hz)
  have hvar := (norm_expSum_sub_expSum_le_frequency_mass S w f u v).trans
    (mul_le_mul_of_nonneg_right hd (sum_nonneg (fun i hi =>
      mul_nonneg (norm_nonneg _) (abs_nonneg _))))
  exact (norm_le_norm_add_norm_sub' _ _).trans (add_le_add hsample hvar)

end Complex
