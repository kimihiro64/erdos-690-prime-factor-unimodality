/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.LargeHeight
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.SmallHeight

/-! # A uniform resolvent bound for paired logarithmic steps

Splitting at imaginary height one gives an entirely analytic constant sixteen.
The bound includes real-axis zeros and both edges of the closed half-unit strip.
It is a coarse alternative to the optimized constant in Booker's Lemma 4.3
(arXiv:math/0507502), requiring no computational boundary estimate.
-/

namespace Complex

private theorem re_resolvent_pair_eq (w : ℂ) :
    (1 / (1 - w)).re + (1 / (1 + w)).re =
      (1 - w.re) / ((1 - w.re) ^ 2 + w.im ^ 2) +
        (1 + w.re) / ((1 + w.re) ^ 2 + w.im ^ 2) := by
  simp only [one_div, inv_re, normSq_apply, sub_re, add_re, one_re, sub_im, add_im,
    one_im]
  ring

/-- The paired right-hand resolvent controls inverse-square height uniformly in the strip. -/
theorem two_div_le_re_resolvent_pair {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    2 / (9 / 4 + w.im ^ 2) ≤ (1 / (1 - w)).re + (1 / (1 + w)).re := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hw
  have hd : (0 : ℝ) < 9 / 4 + w.im ^ 2 := by positivity
  have hm : 0 < 1 - w.re := by linarith
  have hp : 0 < 1 + w.re := by linarith
  have hm2 : 0 < (1 - w.re) ^ 2 + w.im ^ 2 := by positivity
  have hp2 : 0 < (1 + w.re) ^ 2 + w.im ^ 2 := by positivity
  have hms : (1 - w.re) ^ 2 ≤ 9 / 4 := by nlinarith
  have hps : (1 + w.re) ^ 2 ≤ 9 / 4 := by nlinarith
  have h1 : (1 - w.re) / (9 / 4 + w.im ^ 2) ≤
      (1 - w.re) / ((1 - w.re) ^ 2 + w.im ^ 2) := by
    apply (div_le_div_iff₀ hd hm2).mpr
    nlinarith
  have h2 : (1 + w.re) / (9 / 4 + w.im ^ 2) ≤
      (1 + w.re) / ((1 + w.re) ^ 2 + w.im ^ 2) := by
    apply (div_le_div_iff₀ hd hp2).mpr
    nlinarith
  rw [re_resolvent_pair_eq]
  convert add_le_add h1 h2 using 1
  ring

/-- The complete paired integral is bounded by sixteen times the paired resolvent. -/
theorem logNormStepIntegral_pair_le {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    logNormStepIntegral w + logNormStepIntegral (-w) ≤
      16 * ((1 / (1 - w)).re + (1 / (1 + w)).re) := by
  have hneg : |(-w).re| ≤ 1 / 2 := by simpa only [neg_re, abs_neg] using hw
  have hr := two_div_le_re_resolvent_pair hw
  have hd : (0 : ℝ) < 9 / 4 + w.im ^ 2 := by positivity
  by_cases hv : |w.im| ≤ 1
  · have h1 := logNormStepIntegral_le_four hw hv
    have h2 := logNormStepIntegral_le_four hneg (by simpa only [neg_im, abs_neg] using hv)
    have hs : w.im ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hv).1, (abs_le.mp hv).2]
    have hh : (1 / 2 : ℝ) ≤ 2 / (9 / 4 + w.im ^ 2) :=
      (le_div_iff₀ hd).mpr (by nlinarith)
    linarith
  · have hlarge : 1 < |w.im| := lt_of_not_ge hv
    have hne : w.im ≠ 0 := by intro he; norm_num [he] at hlarge
    have hs : 1 ≤ w.im ^ 2 := by nlinarith [sq_abs w.im]
    have h1 := logNormStepIntegral_le_inv_im_sq hw hne
    have h2 := logNormStepIntegral_le_inv_im_sq hneg
      (by simpa only [neg_im, neg_ne_zero] using hne)
    simp only [neg_im, neg_sq] at h2
    have hh : 4 / w.im ^ 2 ≤ 16 * (2 / (9 / 4 + w.im ^ 2)) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (sq_pos_of_ne_zero hne) hd).mpr
      nlinarith
    calc
      _ ≤ 2 / w.im ^ 2 + 2 / w.im ^ 2 := add_le_add h1 h2
      _ = 4 / w.im ^ 2 := by ring
      _ ≤ 16 * (2 / (9 / 4 + w.im ^ 2)) := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by norm_num)

/-- A single nonnegative step is bounded by the same paired resolvent. -/
theorem logNormStepIntegral_le_resolvent_pair {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    logNormStepIntegral w ≤ 16 * ((1 / (1 - w)).re + (1 / (1 + w)).re) := by
  have hn := logNormStepIntegral_nonneg (w := -w) (by
    simp only [neg_re]
    linarith [(abs_le.mp hw).1])
  linarith [logNormStepIntegral_pair_le hw]

end Complex
