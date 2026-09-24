/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.Choose.Sum
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.AbsoluteMoments

/-! # Gaussian integrals of two shifted absolute powers

Two binomial expansions reduce these integrals to a finite sum of exact
absolute Gaussian moments. The shifts are arbitrary real numbers and the
orders are arbitrary natural numbers, including zero.
-/

open MeasureTheory Finset

namespace Real

private theorem shifted_powers_gaussian_eq_sum (m k : ℕ) (a c b x : ℝ) :
    (a + |x|) ^ m * (c + |x|) ^ k * exp (-b * x ^ 2) =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1),
        ((m.choose i : ℝ) * a ^ (m - i) * (k.choose j : ℝ) * c ^ (k - j)) *
          (|x| ^ (i + j) * exp (-b * x ^ 2)) := by
  rw [add_comm a, add_comm c, add_pow, add_pow]
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- Products of shifted absolute powers are integrable against a Gaussian. -/
theorem integrable_add_abs_pow_mul_add_abs_pow_mul_exp_neg_mul_sq
    (m k : ℕ) (a c : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (a + |x|) ^ m * (c + |x|) ^ k * exp (-b * x ^ 2)) := by
  simp_rw [shifted_powers_gaussian_eq_sum]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (integrable_abs_pow_mul_exp_neg_mul_sq (i + j) hb).const_mul _

/-- An explicit finite Gamma sum evaluates a product of shifted absolute powers. -/
theorem integral_add_abs_pow_mul_add_abs_pow_mul_exp_neg_mul_sq
    (m k : ℕ) (a c : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, (a + |x|) ^ m * (c + |x|) ^ k * exp (-b * x ^ 2)) =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1),
        ((m.choose i : ℝ) * a ^ (m - i) * (k.choose j : ℝ) * c ^ (k - j)) *
          ((1 / b) ^ ((((i + j : ℕ) : ℝ) + 1) / 2) *
            Gamma ((((i + j : ℕ) : ℝ) + 1) / 2)) := by
  simp_rw [shifted_powers_gaussian_eq_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ =>
      (integrable_abs_pow_mul_exp_neg_mul_sq (i + j) hb).const_mul _))]
  apply sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_abs_pow_mul_exp_neg_mul_sq (i + j) hb).const_mul _)]
  apply sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_abs_pow_mul_exp_neg_mul_sq (i + j) hb]

end Real
