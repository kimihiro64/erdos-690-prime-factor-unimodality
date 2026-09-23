/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Horizontal decay of Dirichlet series with a lower support bound

Moving right from an absolutely convergent line multiplies each term by
a negative power of its index. A positive lower bound for the support
therefore gives a uniform exponential factor, decaying when that bound
exceeds one. Only Mathlib's term norm, power monotonicity and absolutely
convergent sum comparison are needed.
-/

namespace LSeries

open Complex

/-- A lower support bound gives a uniform horizontal factor for each term. -/
theorem norm_term_le_rpow_mul_of_support {f : ℕ → ℂ} {B σ : ℝ} {s : ℂ}
    (hB : 0 < B) (hs : σ ≤ s.re)
    (hsupport : ∀ n : ℕ, n ≠ 0 → f n ≠ 0 → B ≤ (n : ℝ)) (n : ℕ) :
    ‖term f s n‖ ≤ B ^ (σ - s.re) * ‖term f (σ : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hf : f n = 0
  · simp [hn, hf]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hr := Real.rpow_le_rpow_of_nonpos hB (hsupport n hn hf) (sub_nonpos.mpr hs)
  simp only [norm_term_eq, ite_eq_right hn, ofReal_re]
  calc
    ‖f n‖ / (n : ℝ) ^ s.re =
        (n : ℝ) ^ (σ - s.re) * (‖f n‖ / (n : ℝ) ^ σ) := by
      rw [Real.rpow_sub hnpos]
      field_simp [(Real.rpow_pos_of_pos hnpos σ).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (by positivity)

/-- Sum the termwise horizontal bound on any line to the right of convergence. -/
theorem norm_le_rpow_mul_tsum_norm_of_support {f : ℕ → ℂ} {B σ : ℝ} {s : ℂ}
    (hB : 0 < B) (hs : σ ≤ s.re)
    (hsupport : ∀ n : ℕ, n ≠ 0 → f n ≠ 0 → B ≤ (n : ℝ))
    (hf : LSeriesSummable f (σ : ℂ)) :
    ‖LSeries f s‖ ≤ B ^ (σ - s.re) * ∑' n, ‖term f (σ : ℂ) n‖ := by
  have hfs : LSeriesSummable f s := hf.of_re_le_re hs
  calc
    _ ≤ ∑' n, ‖term f s n‖ := norm_tsum_le_tsum_norm hfs.norm
    _ ≤ ∑' n, B ^ (σ - s.re) * ‖term f (σ : ℂ) n‖ :=
      Summable.tsum_le_tsum (norm_term_le_rpow_mul_of_support hB hs hsupport)
        hfs.norm (hf.norm.mul_left _)
    _ = _ := tsum_mul_left

end LSeries
