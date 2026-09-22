/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Inversion

/-! # Bounds and cancellation for the shifted Laplace contour weight

For a contour strictly between zero and the transform parameter, quadratic
decay in `s-z` also gives quadratic decay in `z`, with an explicit constant.
The integral of the pole-subtracted weight itself vanishes by inversion at
zero. This removes the constant in a genus-one Hadamard expansion.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- Transfer inverse-square decay between complementary arguments separated from zero. -/
theorem div_sq_norm_sub_le {s z : ℂ} {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hz : z ≠ 0) (hv : a ≤ ‖s - z‖) :
    M / (a * ‖s - z‖ ^ 2) ≤
      (M / a * (1 + ‖s‖ / a) ^ 2) / ‖z‖ ^ 2 := by
  have hn : 0 < ‖s - z‖ := ha.trans_le hv
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hratio : ‖s‖ ≤ (‖s‖ / a) * ‖s - z‖ := by
    calc
      ‖s‖ = (‖s‖ / a) * a := (div_mul_cancel₀ _ ha.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  have htriangle : ‖z‖ ≤ (1 + ‖s‖ / a) * ‖s - z‖ := by
    have ht : ‖z‖ ≤ ‖s‖ + ‖s - z‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le s (s - z)
    nlinarith
  have hsq : ‖z‖ ^ 2 ≤ (1 + ‖s‖ / a) ^ 2 * ‖s - z‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg z) htriangle 2
  rw [div_le_div_iff₀ (mul_pos ha (sq_pos_of_pos hn)) (sq_pos_of_pos hzn)]
  calc
    _ ≤ M * ((1 + ‖s‖ / a) ^ 2 * ‖s - z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hM
    _ = _ := by field_simp

/-- Explicit quadratic bound in the contour variable, not just the shifted argument. -/
theorem norm_finiteLaplace_sub_pole_contour_le {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {s : ℂ} {c : ℝ} (hc : 0 < c) (hcs : c < s.re) (t : ℝ) :
    ‖finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
      f 0 / (s - ((c : ℂ) + (t : ℂ) * I))‖ ≤
      (M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2) /
        ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 := by
  have hre : (s - ((c : ℂ) + (t : ℂ) * I)).re = s.re - c := by simp
  have hz : (c : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro heq
    have he := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_re] at he
    exact hc.ne' he
  have hb := norm_finiteLaplace_sub_pole_le_div_re hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (s := s - ((c : ℂ) + (t : ℂ) * I))
    (by rw [hre]; exact sub_pos.mpr hcs)
  rw [hre] at hb
  exact hb.trans (div_sq_norm_sub_le (sub_pos.mpr hcs) hM hz
    (by simpa only [hre] using re_le_norm (s - ((c : ℂ) + (t : ℂ) * I))))

/-- The shifted contour weight is absolutely integrable with the negative height convention. -/
theorem integrable_finiteLaplace_sub_pole_contour {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {s : ℂ} {c : ℝ} (hcs : c < s.re) :
    Integrable (fun t : ℝ => finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
      f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) := by
  have hv := integrable_finiteLaplace_sub_pole_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (s := s - c) (by simpa using sub_pos.mpr hcs)
  simpa only [ofReal_neg, neg_mul, sub_eq_add_neg, neg_add, add_assoc] using hv.comp_neg

/-- Inversion at zero cancels the constant term of a regularized logarithmic derivative. -/
theorem integral_finiteLaplace_sub_pole_contour_eq_zero {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {s : ℂ} {c : ℝ} (hcs : c < s.re) :
    (∫ t : ℝ, finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
      f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) = 0 := by
  have hi := integral_finiteLaplace_sub_pole_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (s := s - c) (by simpa using sub_pos.mpr hcs) 0
  rw [finiteLaplaceRemainderSource_of_nonpos f d le_rfl] at hi
  simp only [ofReal_zero, mul_zero, exp_zero, one_mul] at hi
  have hc₀ : (1 / (2 * (Real.pi : ℂ))) ≠ 0 := by
    exact one_div_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hi₀ := (mul_eq_zero.mp hi).resolve_left hc₀
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding
    (fun t : ℝ => finiteLaplace f d ((s - c) + (t : ℂ) * I) -
      f 0 / ((s - c) + (t : ℂ) * I))
  simpa only [ofReal_neg, neg_mul, sub_eq_add_neg, neg_add, add_assoc] using hneg.trans hi₀

end

end Complex
