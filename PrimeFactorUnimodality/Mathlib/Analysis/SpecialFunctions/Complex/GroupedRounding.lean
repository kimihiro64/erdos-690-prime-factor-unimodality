/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedExponential

/-! # Rounding shared exponential moments and group phases

Moment errors are weighted by the actual evaluation powers. Phase errors
use the norm of the rounded polynomial, so no exact coefficient evaluation
or exact transcendental phase is hidden in the error budget.
-/

namespace Complex

noncomputable section

open Finset

variable {ι κ : Type*} [DecidableEq κ]

/-- A unit phase permits independent errors in the value and phase factor. -/
theorem norm_unit_mul_sub_mul_le {p : ℂ} (hp : ‖p‖ = 1) (z q a : ℂ) :
    ‖p * z - a * q‖ ≤ ‖z - q‖ + ‖q‖ * ‖p - a‖ := by
  have he : p * z - a * q = p * (z - q) + (p - a) * q := by ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul, hp]; ring)

/-- Every stored coefficient and every approximated group phase contributes to the error. -/
theorem norm_groupedExpPolynomial_sub_rounded_le
    (S : Finset ι) (B : Finset κ) (bin : ι → κ) (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ)
    (m : ℕ) (v : ℝ) (a : κ → ℕ → ℂ) (p : κ → ℂ) (ε : κ → ℕ → ℝ) (δ : κ → ℝ)
    (ha : ∀ b ∈ B, ∀ j ∈ range m,
      ‖expSumMoment (S.filter (fun n => bin n = b)) w (fun n => f n - c b) j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖groupedExpPolynomial S B bin w f c m v -
      ∑ b ∈ B, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      ∑ b ∈ B, ((∑ j ∈ range m, ε b j * |v| ^ j) +
        ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  unfold groupedExpPolynomial
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro b hb
  exact (norm_unit_mul_sub_mul_le (norm_exp_I_mul_ofReal (v * c b)) _ _ _).trans
    (add_le_add (norm_expSumPolynomial_sub_rounded_le _ _ _ _ _ _ _ (ha b hb))
      (mul_le_mul_of_nonneg_left (hp b hb) (norm_nonneg _)))

/-- The true exponential sum has the sum of the truncation and rounded-evaluation errors. -/
theorem norm_expSum_sub_roundedGrouped_le
    (S : Finset ι) (B : Finset κ) (bin : ι → κ) (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ)
    (hbin : ∀ n ∈ S, bin n ∈ B) {A v : ℝ} (hA : 0 ≤ A)
    (hres : ∀ n ∈ S, |v * (f n - c (bin n))| ≤ A)
    (m : ℕ) (a : κ → ℕ → ℂ) (p : κ → ℂ) (ε : κ → ℕ → ℝ) (δ : κ → ℝ)
    (ha : ∀ b ∈ B, ∀ j ∈ range m,
      ‖expSumMoment (S.filter (fun n => bin n = b)) w (fun n => f n - c b) j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) -
      ∑ b ∈ B, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      (∑ n ∈ S, ‖w n‖) * (A ^ m * Real.exp A) +
        ∑ b ∈ B, ((∑ j ∈ range m, ε b j * |v| ^ j) +
          ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ (groupedExpPolynomial S B bin w f c m v) _).trans
    (add_le_add (norm_expSum_sub_grouped_le S B bin w f c hbin hA hres m)
      (norm_groupedExpPolynomial_sub_rounded_le S B bin w f c m v a p ε δ ha hp))

end

end Complex
