import PrimeFactorUnimodality.Helpers.Analytic.DigammaHadamardIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.RightResolventIntegral

/-! # Vanishing of the reflected shifted-digamma contour pairing

Height reflection preserves the quadratic contour bound. Absolute
Hadamard interchange applies to the reflected weight; reflecting each
atom back places its pole strictly right of the contour, where the
one-sided inverse Laplace source makes its integral zero.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

variable {f g h : ℝ → ℂ} {d M : ℝ}
  (hd : 0 ≤ d) (hM : 0 ≤ M)
  (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
  (hh : ContinuousOn h (Icc 0 d))
  (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
  (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
  (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
  (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
  {s : ℂ} {c : ℝ} (hc : 0 < c) (hcs : c < s.re)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs

private theorem reflected_contour_bound (t : ℝ) :
    ‖finiteLaplace f d (s - ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) -
      f 0 / (s - ((c : ℂ) + ((-t : ℝ) : ℂ) * I))‖ ≤
      (M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2) /
        ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 := by
  have hn : ‖(c : ℂ) + ((-t : ℝ) : ℂ) * I‖ = ‖(c : ℂ) + (t : ℂ) * I‖ := by
    rw [show (c : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((c : ℂ) + (t : ℂ) * I) by simp]
    exact norm_conj _
  simpa only [hn] using norm_finiteLaplace_sub_pole_contour_le hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hc hcs (-t)

/-- The reflected shifted-digamma integrand is absolutely integrable. -/
theorem integrable_finiteLaplace_mul_reflected_digamma :
    Integrable (fun t : ℝ => (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      digamma (((c : ℂ) - (t : ℂ) * I) / 2 + 1)) := by
  have hH := integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  have hi := integrable_mul_digamma_half_add_one hc hC hH.comp_neg
    (reflected_contour_bound hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs)
  simpa only [neg_neg, ofReal_neg, neg_mul, sub_eq_add_neg] using hi.comp_neg

/-- Every reflected gamma pole pairs to zero, hence so does their complete shifted series. -/
theorem integral_finiteLaplace_mul_reflected_digamma_eq_zero :
    (∫ t : ℝ, (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      digamma (((c : ℂ) - (t : ℂ) * I) / 2 + 1)) = 0 := by
  let H : ℝ → ℂ := fun t => finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
    f 0 / (s - ((c : ℂ) + (t : ℂ) * I))
  have hH : Integrable H := integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  have hz : (∫ t : ℝ, H (-t)) = 0 := by
    rw [integral_neg_eq_self]
    exact integral_finiteLaplace_sub_pole_contour_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs
  have hi := integral_mul_digamma_half_add_one_eq_tsum hc hC hH.comp_neg
    (reflected_contour_bound hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs) hz
  have hflip : (∫ t : ℝ, H (-t) * digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) =
      ∫ t : ℝ, H t * digamma (((c : ℂ) - (t : ℂ) * I) / 2 + 1) := by
    simpa only [ofReal_neg, neg_mul, sub_neg_eq_add] using integral_neg_eq_self
      (fun t : ℝ => H t * digamma (((c : ℂ) - (t : ℂ) * I) / 2 + 1)) volume
  rw [hflip] at hi
  have hatom (n : ℕ) : (∫ t : ℝ, H (-t) *
      (1 / ((c : ℂ) + (t : ℂ) * I - shiftedGammaPole n) + 1 / shiftedGammaPole n)) = 0 := by
    have hn := integral_neg_eq_self (fun t : ℝ => H t *
      (1 / ((c : ℂ) - (t : ℂ) * I - shiftedGammaPole n) + 1 / shiftedGammaPole n)) volume
    simp only [ofReal_neg, neg_mul, sub_neg_eq_add] at hn
    rw [hn]
    exact integral_finiteLaplace_sub_pole_mul_reflected_atom_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs ((shiftedGammaPole_re_nonpos n).trans_lt hc)
  simpa only [hatom, tsum_zero, mul_zero] using hi

end

end PrimeFactorUnimodality
