/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Basic

/-! # Absolute interchange of a Dirichlet series with a vertical integral

The norm of each Dirichlet term is constant along a vertical line. An
integrable contour weight and absolute convergence at its real part
therefore give the full Fubini bound, not an assumed interchange identity.
-/

namespace LSeries

noncomputable section

open Complex MeasureTheory

/-- Nonzero Dirichlet terms in exponential form, with the real logarithm of the index. -/
theorem term_eq_mul_exp {n : ℕ} (hn : n ≠ 0) (f : ℕ → ℂ) (s : ℂ) :
    term f s n = f n * exp (-s * (Real.log n : ℂ)) := by
  rw [term_of_ne_zero hn, cpow_def_of_ne_zero (by exact_mod_cast hn), ← natCast_log]
  simp only [div_eq_mul_inv, ← exp_neg]
  congr 2
  ring

/-- Multiplication by an exponential changes the Dirichlet parameter by exactly its exponent. -/
theorem term_mul_exp (f : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    term f s n * exp (-w * (Real.log n : ℂ)) = term f (s + w) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [term_eq_mul_exp hn, term_eq_mul_exp hn, mul_assoc, ← exp_add]
    congr 2
    ring

/-- A Dirichlet term varies continuously along every vertical line, including the zero term. -/
theorem continuous_term_vertical (f : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => term f ((c : ℂ) + (t : ℂ) * I) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [term_zero]
    exact continuous_const
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [term_of_ne_zero hn, cpow_def_of_ne_zero hn']
    exact continuous_const.div (by fun_prop) (fun _ => exp_ne_zero _)

/-- Multiplying one term by an integrable contour weight preserves integrability. -/
theorem integrable_term_vertical_mul (f : ℕ → ℂ) (c : ℝ) (n : ℕ)
    {K : ℝ → ℂ} (hK : Integrable K) :
    Integrable (fun t : ℝ => term f ((c : ℂ) + (t : ℂ) * I) n * K t) := by
  apply (hK.norm.const_mul ‖term f (c : ℂ) n‖).mono'
    ((continuous_term_vertical f c n).aestronglyMeasurable.mul hK.aestronglyMeasurable)
  filter_upwards with t
  simp [norm_term_eq]

/-- The integrated absolute norms factor exactly into the coefficient norm and the weight norm. -/
theorem integral_norm_term_vertical_mul (f : ℕ → ℂ) (c : ℝ) (n : ℕ) (K : ℝ → ℂ) :
    (∫ t : ℝ, ‖term f ((c : ℂ) + (t : ℂ) * I) n * K t‖) =
      ‖term f (c : ℂ) n‖ * ∫ t : ℝ, ‖K t‖ := by
  simp only [norm_mul, norm_term_eq, add_re, ofReal_re, mul_re, I_re, I_im,
    ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact integral_const_mul _ _

/-- Absolute summability of the integrated term norms is derived from the real-axis series. -/
theorem summable_integral_norm_term_vertical_mul {f : ℕ → ℂ} {c : ℝ}
    (hf : LSeriesSummable f (c : ℂ)) (K : ℝ → ℂ) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖term f ((c : ℂ) + (t : ℂ) * I) n * K t‖) := by
  simp only [integral_norm_term_vertical_mul]
  exact hf.norm.mul_right _

/-- Interchange of the entire absolutely convergent Dirichlet series and a weighted contour. -/
theorem tsum_integral_term_vertical_mul {f : ℕ → ℂ} {c : ℝ}
    (hf : LSeriesSummable f (c : ℂ)) {K : ℝ → ℂ} (hK : Integrable K) :
    (∑' n : ℕ, ∫ t : ℝ, term f ((c : ℂ) + (t : ℂ) * I) n * K t) =
      ∫ t : ℝ, LSeries f ((c : ℂ) + (t : ℂ) * I) * K t := by
  rw [integral_tsum_of_summable_integral_norm
    (fun n => integrable_term_vertical_mul f c n hK)
    (summable_integral_norm_term_vertical_mul hf K)]
  apply integral_congr_ae
  filter_upwards with t
  exact tsum_mul_right

end

end LSeries
