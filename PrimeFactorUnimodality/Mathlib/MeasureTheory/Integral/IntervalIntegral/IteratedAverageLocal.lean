/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageComplex

/-! # The complex averaging recurrence on a positive half-line

A continuous extension by the left endpoint supplies integrability.
Local support congruence then removes the extension from the recurrence.
-/

open Complex MeasureTheory Set

namespace intervalIntegral

noncomputable section

/-- The complex recurrence needs continuity only to the right of the evaluation point. -/
theorem iteratedBoxAverageComplex_succ_on_Ici {a h x : ℝ} (hh : 0 ≤ h)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ici a)) (hx : a ≤ x) (n : ℕ) :
    iteratedBoxAverageComplex h (n + 1) f x =
      (h⁻¹ : ℝ) * ∫ u in (0 : ℝ)..h, iteratedBoxAverageComplex h n f (x + u) := by
  let F : ℝ → ℂ := fun t => f (max a t)
  have hF : Continuous F := hf.comp_continuous (continuous_const.max continuous_id)
    (fun t => le_max_left a t)
  have he (k : ℕ) {y : ℝ} (hy : a ≤ y) :
      iteratedBoxAverageComplex h k F y = iteratedBoxAverageComplex h k f y := by
    apply iteratedBoxAverageComplex_congr_on hh
    intro t ht
    simp only [F, max_eq_right (hy.trans ht.1)]
  rw [← he (n + 1) hx, iteratedBoxAverageComplex_succ h hF]
  congr 1
  apply integral_congr
  intro u hu
  rw [uIcc_of_le hh] at hu
  exact he n (by linarith [hu.1])

end

end intervalIntegral
