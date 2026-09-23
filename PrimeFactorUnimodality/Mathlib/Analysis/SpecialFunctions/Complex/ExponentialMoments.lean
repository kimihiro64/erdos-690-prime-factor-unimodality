/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # Shared moments for finite imaginary exponential sums

The finite Taylor coefficients are independent of the evaluation point.
Mathlib's exponential remainder gives a uniform error on any bounded
residual-frequency window, including order zero and empty sums.
-/

namespace Complex

noncomputable section

open Finset

variable {ι : Type*}

/-- Successive Taylor atoms reuse the previous power and factorial quotient. -/
theorem taylorMoment_succ (w z : ℂ) (j : ℕ) :
    w * z ^ (j + 1) / ((j + 1).factorial : ℂ) =
      (w * z ^ j / (j.factorial : ℂ)) * z / (j + 1 : ℂ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- One reusable coefficient of a weighted imaginary exponential sum. -/
def expSumMoment (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ S, w n * (I * (r n : ℂ)) ^ j / (j.factorial : ℂ)

/-- Evaluation of the first moments at a real parameter. -/
def expSumPolynomial (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ) (m : ℕ) (v : ℝ) : ℂ :=
  ∑ j ∈ range m, expSumMoment S w r j * (v : ℂ) ^ j

/-- Regrouping the polynomial costs no approximation error. -/
theorem expSumPolynomial_eq_sum (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ)
    (m : ℕ) (v : ℝ) :
    expSumPolynomial S w r m v =
      ∑ n ∈ S, w n * ∑ j ∈ range m, (I * ((v * r n : ℝ) : ℂ)) ^ j / j.factorial := by
  unfold expSumPolynomial expSumMoment
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  simp only [ofReal_mul, mul_pow]
  ring

/-- A single imaginary exponential has a uniform geometric Taylor remainder. -/
theorem norm_exp_imaginary_sub_sum_le {v r a : ℝ} (ha : 0 ≤ a)
    (h : |v * r| ≤ a) (m : ℕ) :
    ‖exp (I * ((v * r : ℝ) : ℂ)) -
      ∑ j ∈ range m, (I * ((v * r : ℝ) : ℂ)) ^ j / j.factorial‖ ≤
        a ^ m * Real.exp a := by
  have hn : ‖I * ((v * r : ℝ) : ℂ)‖ = |v * r| := by simp
  have he := norm_exp_sub_sum_le_norm_mul_exp (I * ((v * r : ℝ) : ℂ)) m
  rw [hn] at he
  exact he.trans (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h m)
    (Real.exp_le_exp.mpr h) (Real.exp_pos _).le (pow_nonneg ha _))

/-- The complete finite sum is controlled by its total coefficient mass. -/
theorem norm_expSum_sub_polynomial_le (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ)
    {a v : ℝ} (ha : 0 ≤ a) (h : ∀ n ∈ S, |v * r n| ≤ a) (m : ℕ) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * r n : ℝ) : ℂ))) -
      expSumPolynomial S w r m v‖ ≤
        (∑ n ∈ S, ‖w n‖) * (a ^ m * Real.exp a) := by
  rw [expSumPolynomial_eq_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S, ‖w n * exp (I * ((v * r n : ℝ) : ℂ)) -
        w n * ∑ j ∈ range m, (I * ((v * r n : ℝ) : ℂ)) ^ j / j.factorial‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖w n‖ * (a ^ m * Real.exp a) := by
      apply sum_le_sum
      intro n hn
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_exp_imaginary_sub_sum_le ha (h n hn) m)
        (norm_nonneg _)
    _ = _ := (sum_mul ..).symm

/-- Independent errors in stored moments accumulate with the actual evaluation powers. -/
theorem norm_expSumPolynomial_sub_rounded_le (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ)
    (m : ℕ) (v : ℝ) (c : ℕ → ℂ) (ε : ℕ → ℝ)
    (hc : ∀ j ∈ range m, ‖expSumMoment S w r j - c j‖ ≤ ε j) :
    ‖expSumPolynomial S w r m v - ∑ j ∈ range m, c j * (v : ℂ) ^ j‖ ≤
      ∑ j ∈ range m, ε j * |v| ^ j := by
  unfold expSumPolynomial
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [← sub_mul, norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hc j hj) (pow_nonneg (abs_nonneg _) _)

end

end Complex
