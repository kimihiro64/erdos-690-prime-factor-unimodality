/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageComplex

/-! # Perturbation bounds through iterated complex averages

A uniform pointwise error passes through every averaging order unchanged.
Only continuity on a containing half-line is required. In particular, the
bound does not inherit the inverse-step powers of a difference formula.
-/

namespace intervalIntegral

open Complex Set MeasureTheory

noncomputable section

/-- Subtraction commutes with averages of continuous complex functions. -/
theorem iteratedBoxAverageComplex_sub (h : ℝ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (n : ℕ) (x : ℝ) :
    iteratedBoxAverageComplex h n (fun t => f t - g t) x =
      iteratedBoxAverageComplex h n f x - iteratedBoxAverageComplex h n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedBoxAverageComplex_succ h (show Continuous (fun t => f t - g t) from hf.sub hg),
      iteratedBoxAverageComplex_succ h hf, iteratedBoxAverageComplex_succ h hg]
    simp_rw [ih]
    rw [integral_sub]
    · ring
    · exact ((continuous_iteratedBoxAverageComplex h hf n).comp
        (continuous_const.add continuous_id)).intervalIntegrable _ _
    · exact ((continuous_iteratedBoxAverageComplex h hg n).comp
        (continuous_const.add continuous_id)).intervalIntegrable _ _

/-- Half-line continuity suffices because every average uses only its finite support. -/
theorem iteratedBoxAverageComplex_sub_on_Ici {h a x : ℝ} (hh : 0 ≤ h)
    {f g : ℝ → ℂ} (hf : ContinuousOn f (Ici a)) (hg : ContinuousOn g (Ici a))
    (hax : a ≤ x) (n : ℕ) :
    iteratedBoxAverageComplex h n (fun t => f t - g t) x =
      iteratedBoxAverageComplex h n f x - iteratedBoxAverageComplex h n g x := by
  let F : ℝ → ℂ := fun t => f (max a t)
  let G : ℝ → ℂ := fun t => g (max a t)
  have hF : Continuous F := hf.comp_continuous (continuous_const.max continuous_id)
    (fun t => le_max_left a t)
  have hG : Continuous G := hg.comp_continuous (continuous_const.max continuous_id)
    (fun t => le_max_left a t)
  have heF : EqOn F f (Icc x (x + n * h)) := by
    intro t ht
    simp only [F, max_eq_right (hax.trans ht.1)]
  have heG : EqOn G g (Icc x (x + n * h)) := by
    intro t ht
    simp only [G, max_eq_right (hax.trans ht.1)]
  have he : EqOn (fun t => F t - G t) (fun t => f t - g t)
      (Icc x (x + n * h)) := fun t ht => by
        change F t - G t = f t - g t
        rw [heF ht, heG ht]
  rw [← iteratedBoxAverageComplex_congr_on hh n he,
    iteratedBoxAverageComplex_sub h hF hG,
    iteratedBoxAverageComplex_congr_on hh n heF,
    iteratedBoxAverageComplex_congr_on hh n heG]

/-- Every averaging order preserves a uniform pointwise error bound on its support. -/
theorem norm_iteratedBoxAverageComplex_sub_le_on_Ici {h a x C : ℝ} (hh : 0 < h)
    {f g : ℝ → ℂ} (hf : ContinuousOn f (Ici a)) (hg : ContinuousOn g (Ici a))
    (hax : a ≤ x) (n : ℕ)
    (hbound : ∀ t ∈ Icc x (x + n * h), ‖f t - g t‖ ≤ C) :
    ‖iteratedBoxAverageComplex h n f x - iteratedBoxAverageComplex h n g x‖ ≤ C := by
  rw [← iteratedBoxAverageComplex_sub_on_Ici hh.le hf hg hax n]
  exact norm_iteratedBoxAverageComplex_le_on_Ici hh (hf.sub hg) hax n hbound

end

end intervalIntegral
