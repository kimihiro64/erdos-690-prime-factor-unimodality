import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.HorizontalDecay

/-! # Exact interfaces and boundary tests for horizontal zeta logarithms -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex LSeries

example {f : ℕ → ℂ} {B σ : ℝ} {s : ℂ}
    (hB : 0 < B) (hs : σ ≤ s.re)
    (hsupport : ∀ n : ℕ, n ≠ 0 → f n ≠ 0 → B ≤ (n : ℝ)) (n : ℕ) :
    ‖term f s n‖ ≤ B ^ (σ - s.re) * ‖term f (σ : ℂ) n‖ := by
  exact LSeries.norm_term_le_rpow_mul_of_support hB hs hsupport n

example {f : ℕ → ℂ} {B σ : ℝ} {s : ℂ}
    (hB : 0 < B) (hs : σ ≤ s.re)
    (hsupport : ∀ n : ℕ, n ≠ 0 → f n ≠ 0 → B ≤ (n : ℝ))
    (hf : LSeriesSummable f (σ : ℂ)) :
    ‖LSeries f s‖ ≤ B ^ (σ - s.re) * ∑' n, ‖term f (σ : ℂ) n‖ := by
  exact LSeries.norm_le_rpow_mul_tsum_norm_of_support hB hs hsupport hf


example {f : ℕ → ℂ} {B σ : ℝ} (hB : 0 < B)
    (hsupport : ∀ n : ℕ, n ≠ 0 → f n ≠ 0 → B ≤ (n : ℝ))
    (hf : LSeriesSummable f (σ : ℂ)) (T : ℝ) :
    ‖LSeries f ((σ : ℂ) + T * I)‖ ≤ ∑' n, ‖term f (σ : ℂ) n‖ := by
  simpa using norm_le_rpow_mul_tsum_norm_of_support
    (s := (σ : ℂ) + T * I) hB (by simp) hsupport hf

example {B σ : ℝ} {s : ℂ} (hB : 0 < B) (hs : σ ≤ s.re) (n : ℕ) :
    ‖term (fun _ => (0 : ℂ)) s n‖ ≤
      B ^ (σ - s.re) * ‖term (fun _ => (0 : ℂ)) (σ : ℂ) n‖ := by
  exact norm_term_le_rpow_mul_of_support hB hs (by simp) n

example {f : ℕ → ℂ} {B σ : ℝ} {s : ℂ} (hB : 0 < B) (hs : σ ≤ s.re)
    (hsupport : ∀ n : ℕ, n ≠ 0 → f n ≠ 0 → B ≤ (n : ℝ)) :
    ‖term f s 0‖ ≤ B ^ (σ - s.re) * ‖term f (σ : ℂ) 0‖ := by
  exact norm_term_le_rpow_mul_of_support hB hs hsupport 0

end

end PrimeFactorUnimodality.Tests
