/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.Linarith

/-! # Trigonometric positivity for the zeta logarithmic derivative

A nonnegative cosine polynomial gives a nonnegative linear combination of
the real parts of `-ζ'/ζ`. The proof uses the absolutely convergent von
Mangoldt series on `Re(s) > 1`. This is the positivity ingredient of the
classical and optimized explicit zero-free-region arguments.
-/

open Complex
open scoped BigOperators

namespace ArithmeticFunction

/-- The real part of a von Mangoldt Dirichlet term on a vertical line. -/
theorem re_vonMangoldt_term (σ t : ℝ) (n : ℕ) :
    (LSeries.term (fun n => (vonMangoldt n : ℂ)) ((σ : ℂ) + t * I) n).re =
      vonMangoldt n * Real.exp (-σ * Real.log n) * Real.cos (t * Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_def₀ (by simp), cpow_def_of_ne_zero (by exact_mod_cast hn),
    ← natCast_log]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_re,
    neg_re, neg_im, add_re, add_im, mul_im, I_re, I_im, mul_zero, mul_one,
    add_zero, zero_add]
  rw [mul_comm (Real.log n) (-σ),
    show Real.log n * -t = -(t * Real.log n) by ring, Real.cos_neg]
  ring

end ArithmeticFunction

open scoped ComplexOrder in
/-- The absolutely convergent logarithmic derivative is bounded by its real-axis value. -/
theorem norm_neg_logDeriv_riemannZeta_le_real {s : ℂ} (hs : 1 < s.re) :
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hreal := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (show 1 < (s.re : ℂ).re from hs)
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (show 1 < (s.re : ℂ).re from hs), LSeries, LSeries, re_tsum hreal]
  calc
    ‖∑' n, LSeries.term f s n‖ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n, (LSeries.term f (s.re : ℂ) n).re := by
      apply tsum_congr
      intro n
      have hnorm : ‖LSeries.term f s n‖ = ‖LSeries.term f (s.re : ℂ) n‖ := by
        simp only [LSeries.norm_term_eq, ofReal_re]
      rw [hnorm]
      have hn : 0 ≤ LSeries.term f (s.re : ℂ) n := LSeries.term_nonneg
        (by simpa only [f, zero_le_real] using ArithmeticFunction.vonMangoldt_nonneg (n := n)) _
      exact (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hn)).symm

/-- Every nonnegative cosine polynomial yields a zeta logarithmic-derivative inequality. -/
theorem sum_mul_re_neg_logDeriv_riemannZeta_nonneg {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (k : ι → ℝ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ s, a i * Real.cos (k i * u)) :
    0 ≤ ∑ i ∈ s, a i *
      (-deriv riemannZeta ((σ : ℂ) + (k i * t : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (k i * t : ℝ) * I)).re := by
  let term : ι → ℕ → ℂ := fun i =>
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((σ : ℂ) + (k i * t : ℝ) * I)
  have hs : ∀ i : ι, Summable (term i) := by
    intro i
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have heq : ∀ i : ι,
      (-deriv riemannZeta ((σ : ℂ) + (k i * t : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (k i * t : ℝ) * I)).re = ∑' n, (term i n).re := by
    intro i
    rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by simpa using hσ), LSeries, re_tsum (hs i)]
  simp_rw [heq, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum
    (fun i _ => (Complex.hasSum_re (hs i).hasSum).summable.mul_left (a i))]
  apply tsum_nonneg
  intro n
  simp only [term, ArithmeticFunction.re_vonMangoldt_term]
  have heq' : (∑ i ∈ s, a i * (ArithmeticFunction.vonMangoldt n *
      Real.exp (-σ * Real.log n) * Real.cos (k i * t * Real.log n))) =
        (ArithmeticFunction.vonMangoldt n * Real.exp (-σ * Real.log n)) *
          ∑ i ∈ s, a i * Real.cos (k i * (t * Real.log n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc (k i) t (Real.log n)]
    ring
  rw [heq']
  exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.exp_pos _).le) (hpoly _)

/-- The classical `3 + 4 cos u + cos (2u)` logarithmic-derivative inequality. -/
theorem three_four_one_re_neg_logDeriv_riemannZeta_nonneg
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv riemannZeta ((σ : ℂ) + t * I) /
        riemannZeta ((σ : ℂ) + t * I)).re +
      (-deriv riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)).re := by
  have h := sum_mul_re_neg_logDeriv_riemannZeta_nonneg
    Finset.univ (![3, 4, 1] : Fin 3 → ℝ) (fun i : Fin 3 => (i.val : ℝ)) hσ t (by
      intro u
      norm_num [Fin.sum_univ_succ]
      rw [Real.cos_two_mul]
      nlinarith [sq_nonneg (1 + Real.cos u)])
  norm_num [Fin.sum_univ_succ, add_assoc] at h ⊢
  exact h
