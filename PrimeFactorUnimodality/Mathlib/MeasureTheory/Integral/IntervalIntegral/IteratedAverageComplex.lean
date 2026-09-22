/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageContinuous
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageSupport

/-! # Complex interval averages and their support norm bound

Real and imaginary components reuse the existing real average. For
continuous inputs this is exactly the iterated complex interval integral,
and its norm is bounded by any bound on the complete finite support.
-/

open MeasureTheory Complex Set

namespace intervalIntegral

noncomputable section

def iteratedBoxAverageComplex (h : ℝ) (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ⟨iteratedBoxAverage h n (fun t => (f t).re) x,
    iteratedBoxAverage h n (fun t => (f t).im) x⟩

theorem continuous_iteratedBoxAverageComplex (h : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (n : ℕ) : Continuous (iteratedBoxAverageComplex h n f) := by
  have hr := continuous_ofReal.comp (continuous_iteratedBoxAverage h (continuous_re.comp hf) n)
  have hi := continuous_ofReal.comp (continuous_iteratedBoxAverage h (continuous_im.comp hf) n)
  exact (hr.add (hi.mul_const I)).congr (fun _ => by
    apply Complex.ext <;> simp [iteratedBoxAverageComplex, Function.comp_def])

theorem iteratedBoxAverageComplex_succ (h : ℝ) {f : ℝ → ℂ} (hf : Continuous f)
    (n : ℕ) (x : ℝ) :
    iteratedBoxAverageComplex h (n + 1) f x =
      (h⁻¹ : ℝ) * ∫ u in (0 : ℝ)..h, iteratedBoxAverageComplex h n f (x + u) := by
  have hi : IntervalIntegrable (fun u => iteratedBoxAverageComplex h n f (x + u))
      volume 0 h := ((continuous_iteratedBoxAverageComplex h hf n).comp
    (continuous_const.add continuous_id)).intervalIntegrable 0 h
  apply Complex.ext
  · simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact congrArg (fun t : ℝ => h⁻¹ * t) (Complex.reCLM.intervalIntegral_comp_comm hi)
  · simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    exact congrArg (fun t : ℝ => h⁻¹ * t) (Complex.imCLM.intervalIntegral_comp_comm hi)

theorem iteratedBoxAverageComplex_sub_const {h : ℝ} (hh : h ≠ 0)
    {f : ℝ → ℂ} (hf : Continuous f) (n : ℕ) (c : ℂ) (x : ℝ) :
    iteratedBoxAverageComplex h n (fun t => f t - c) x =
      iteratedBoxAverageComplex h n f x - c := by
  apply Complex.ext
  · exact iteratedBoxAverage_sub_const hh (continuous_re.comp hf) n c.re x
  · exact iteratedBoxAverage_sub_const hh (continuous_im.comp hf) n c.im x

theorem iteratedBoxAverageComplex_congr_on {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {f g : ℝ → ℂ} {x : ℝ} (he : EqOn f g (Icc x (x + n * h))) :
    iteratedBoxAverageComplex h n f x = iteratedBoxAverageComplex h n g x := by
  apply Complex.ext
  · exact iteratedBoxAverage_congr_on hh n (fun t ht => congrArg Complex.re (he ht))
  · exact iteratedBoxAverage_congr_on hh n (fun t ht => congrArg Complex.im (he ht))

theorem norm_iteratedBoxAverageComplex_le {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf : Continuous f) (n : ℕ) {x C : ℝ}
    (hbound : ∀ t ∈ Icc x (x + n * h), ‖f t‖ ≤ C) :
    ‖iteratedBoxAverageComplex h n f x‖ ≤ C := by
  induction n generalizing x with
  | zero => exact hbound x (by simp)
  | succ n ih =>
    rw [iteratedBoxAverageComplex_succ h hf, norm_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    have hi : ‖∫ u in (0 : ℝ)..h, iteratedBoxAverageComplex h n f (x + u)‖ ≤ C * h := by
      have he := norm_integral_le_of_norm_le_const (a := 0) (b := h)
        (f := fun u => iteratedBoxAverageComplex h n f (x + u)) (C := C) (by
          intro u hu
          rw [uIoc_of_le hh.le] at hu
          apply ih
          intro t ht
          apply hbound t
          constructor
          · linarith [ht.1, hu.1]
          · push_cast
            linarith [ht.2, hu.2])
      simpa only [sub_zero, abs_of_pos hh] using he
    calc
      _ ≤ h⁻¹ * (C * h) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hh.le)
      _ = C := by field_simp [hh.ne']

/-- Continuity only to the right of a lower bound suffices for constant subtraction. -/
theorem iteratedBoxAverageComplex_sub_const_on_Ici {h a x : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ici a)) (hax : a ≤ x) (n : ℕ) (c : ℂ) :
    iteratedBoxAverageComplex h n (fun t => f t - c) x =
      iteratedBoxAverageComplex h n f x - c := by
  let F : ℝ → ℂ := fun t => f (max a t)
  have hF : Continuous F := hf.comp_continuous (continuous_const.max continuous_id)
    (fun t => le_max_left a t)
  have he : EqOn F f (Icc x (x + n * h)) := by
    intro t ht
    simp only [F, max_eq_right (hax.trans ht.1)]
  have hec : EqOn (fun t => F t - c) (fun t => f t - c) (Icc x (x + n * h)) :=
    fun t ht => congrArg (fun z => z - c) (he ht)
  rw [← iteratedBoxAverageComplex_congr_on hh.le n hec,
    iteratedBoxAverageComplex_sub_const hh.ne' hF,
    iteratedBoxAverageComplex_congr_on hh.le n he]

/-- The support norm estimate also needs continuity only on a containing half-line. -/
theorem norm_iteratedBoxAverageComplex_le_on_Ici {h a x C : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ici a)) (hax : a ≤ x) (n : ℕ)
    (hbound : ∀ t ∈ Icc x (x + n * h), ‖f t‖ ≤ C) :
    ‖iteratedBoxAverageComplex h n f x‖ ≤ C := by
  let F : ℝ → ℂ := fun t => f (max a t)
  have hF : Continuous F := hf.comp_continuous (continuous_const.max continuous_id)
    (fun t => le_max_left a t)
  have he : EqOn F f (Icc x (x + n * h)) := by
    intro t ht
    simp only [F, max_eq_right (hax.trans ht.1)]
  rw [← iteratedBoxAverageComplex_congr_on hh.le n he]
  exact norm_iteratedBoxAverageComplex_le hh hF n (fun t ht => by rw [he ht]; exact hbound t ht)

end

end intervalIntegral
