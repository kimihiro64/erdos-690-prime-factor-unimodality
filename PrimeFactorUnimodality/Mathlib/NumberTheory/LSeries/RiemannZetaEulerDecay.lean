/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.HorizontalDecay
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerLog

/-! # Horizontal decay of the actual Euler logarithm

The coefficient at one vanishes. Starting on any convergent real line,
the support bound two gives exponential decay, uniformly in imaginary
height. The real part is the logarithm of zeta's modulus, so both signs
of that real logarithm satisfy the same integrable majorant.
-/

open Complex ArithmeticFunction

open scoped ComplexOrder in
/-- The nonnegative real series identifies its absolute mass exactly. -/
theorem tsum_norm_riemannZetaEulerLog_terms {σ : ℝ} (hσ : 1 < σ) :
    (∑' n, ‖LSeries.term (fun n => (vonMangoldt n : ℂ) / Real.log n) (σ : ℂ) n‖) =
      Real.log ‖riemannZeta (σ : ℂ)‖ := by
  rw [← re_riemannZetaEulerLog hσ, riemannZetaEulerLog, LSeries,
    re_tsum (summable_riemannZetaEulerLog hσ)]
  apply tsum_congr
  intro n
  have hc : (0 : ℂ) ≤ (vonMangoldt n : ℂ) / Real.log n := by
    rw [← ofReal_div, zero_le_real]
    exact div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)
  exact (congrArg Complex.re (eq_coe_norm_of_nonneg (LSeries.term_nonneg hc σ))).symm

/-- The complete Euler logarithm decays at least as fast as the first possible index. -/
theorem norm_riemannZetaEulerLog_le_two_rpow {σ : ℝ} {s : ℂ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖riemannZetaEulerLog s‖ ≤ (2 : ℝ) ^ (σ - s.re) * Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hsupport (n : ℕ) (hn : n ≠ 0)
      (hc : (vonMangoldt n : ℂ) / Real.log n ≠ 0) : (2 : ℝ) ≤ n := by
    have hn1 : n ≠ 1 := by intro he; simp [he] at hc
    exact_mod_cast (show 2 ≤ n by omega)
  have h := LSeries.norm_le_rpow_mul_tsum_norm_of_support (by norm_num : (0 : ℝ) < 2)
    hs hsupport (summable_riemannZetaEulerLog hσ)
  rwa [tsum_norm_riemannZetaEulerLog_terms hσ] at h

/-- The real log modulus has the same uniform, two-sided horizontal majorant. -/
theorem abs_log_norm_riemannZeta_le_two_rpow {σ : ℝ} {s : ℂ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    |Real.log ‖riemannZeta s‖| ≤
      (2 : ℝ) ^ (σ - s.re) * Real.log ‖riemannZeta (σ : ℂ)‖ := by
  rw [← re_riemannZetaEulerLog (hσ.trans_le hs)]
  exact (abs_re_le_norm _).trans (norm_riemannZetaEulerLog_le_two_rpow hσ hs)
