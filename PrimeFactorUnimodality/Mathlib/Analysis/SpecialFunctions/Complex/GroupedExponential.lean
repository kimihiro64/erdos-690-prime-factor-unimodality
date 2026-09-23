/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Rat.Floor
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialMoments

/-! # Frequency grouping with a uniform finite-sum error

Factor a unit phase from each frequency group, then evaluate shared residual
moments. Regrouping is exact; only the residual Taylor tails contribute error.
Nearest-integer centers give a half-unit residual for arbitrary real frequencies.
-/

namespace Complex

noncomputable section

open Finset

variable {ι κ : Type*} [DecidableEq κ]

/-- The grouped approximation stores moments once per frequency group. -/
def groupedExpPolynomial (S : Finset ι) (B : Finset κ) (bin : ι → κ)
    (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ) (m : ℕ) (v : ℝ) : ℂ :=
  ∑ b ∈ B, exp (I * ((v * c b : ℝ) : ℂ)) *
    expSumPolynomial (S.filter (fun n => bin n = b)) w (fun n => f n - c b) m v

/-- Factoring each center phase preserves the original sum exactly. -/
theorem expSum_eq_grouped (S : Finset ι) (B : Finset κ) (bin : ι → κ)
    (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ)
    (hbin : ∀ n ∈ S, bin n ∈ B) (v : ℝ) :
    (∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) =
      ∑ b ∈ B, exp (I * ((v * c b : ℝ) : ℂ)) *
        ∑ n ∈ S.filter (fun n => bin n = b),
          w n * exp (I * ((v * (f n - c b) : ℝ) : ℂ)) := by
  rw [← sum_fiberwise_of_maps_to hbin (fun n => w n * exp (I * ((v * f n : ℝ) : ℂ)))]
  apply sum_congr rfl
  intro b hb
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  have he : exp (I * ((v * f n : ℝ) : ℂ)) =
      exp (I * ((v * c b : ℝ) : ℂ)) * exp (I * ((v * (f n - c b) : ℝ) : ℂ)) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The full grouping error depends on residual frequencies, not the largest original frequency. -/
theorem norm_expSum_sub_grouped_le (S : Finset ι) (B : Finset κ) (bin : ι → κ)
    (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ) (hbin : ∀ n ∈ S, bin n ∈ B)
    {a v : ℝ} (ha : 0 ≤ a) (h : ∀ n ∈ S, |v * (f n - c (bin n))| ≤ a) (m : ℕ) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) -
      groupedExpPolynomial S B bin w f c m v‖ ≤
        (∑ n ∈ S, ‖w n‖) * (a ^ m * Real.exp a) := by
  rw [expSum_eq_grouped S B bin w f c hbin v, groupedExpPolynomial, ← sum_sub_distrib]
  calc
    _ ≤ ∑ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) *
        (∑ n ∈ S.filter (fun n => bin n = b),
          w n * exp (I * ((v * (f n - c b) : ℝ) : ℂ))) -
        exp (I * ((v * c b : ℝ) : ℂ)) *
          expSumPolynomial (S.filter (fun n => bin n = b)) w (fun n => f n - c b) m v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b ∈ B, (∑ n ∈ S.filter (fun n => bin n = b), ‖w n‖) *
        (a ^ m * Real.exp a) := by
      apply sum_le_sum
      intro b hb
      rw [← mul_sub, norm_mul, norm_exp_I_mul_ofReal, one_mul]
      apply norm_expSum_sub_polynomial_le _ _ _ ha
      intro n hn
      have hmem := mem_filter.mp hn
      simpa only [hmem.2] using h n hmem.1
    _ = _ := by rw [← sum_mul, sum_fiberwise_of_maps_to hbin]

/-- Rounding a frequency to the nearest integer gives a half-unit residual, including ties. -/
theorem abs_sub_nearestInt_le (x : ℝ) : |x - (⌊x + 1 / 2⌋ : ℤ)| ≤ (1 / 2 : ℝ) := by
  have hlo := Int.floor_le (x + 1 / 2)
  have hhi := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-- Canonical nearest-integer grouping has a geometric error on the entire unit window. -/
theorem norm_expSum_sub_nearestGrouped_le (S : Finset ι) (w : ι → ℂ) (f : ι → ℝ)
    {v : ℝ} (hv : |v| ≤ 1) (m : ℕ) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) -
      groupedExpPolynomial S (S.image (fun n => ⌊f n + 1 / 2⌋))
        (fun n => ⌊f n + 1 / 2⌋) w f (fun k : ℤ => k) m v‖ ≤
      (∑ n ∈ S, ‖w n‖) * ((1 / 2 : ℝ) ^ m * Real.exp (1 / 2)) := by
  classical
  apply norm_expSum_sub_grouped_le _ _ _ _ _ _ (fun n hn => mem_image_of_mem _ hn)
    (by norm_num)
  intro n hn
  rw [abs_mul]
  exact (mul_le_mul hv (abs_sub_nearestInt_le (f n)) (abs_nonneg _) (by norm_num)).trans_eq
    (by ring)

end

end Complex
