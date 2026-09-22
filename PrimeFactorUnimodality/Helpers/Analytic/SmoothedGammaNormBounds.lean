import PrimeFactorUnimodality.Helpers.Analytic.DigammaHeightBounds
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # Two explicit errors for the shifted Gamma factor

Both digamma approximations preserve the coefficient `1-kappa` when
subtracting a positive real shift. The norm-based error decays with height;
the real-part error remains useful at zero and small heights.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

private theorem gammaShift_norm_le {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖s / 2 + 1‖ ≤ ‖(s + (δ : ℂ)) / 2 + 1‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im, div_ofNat_re,
    div_ofNat_im, ofReal_re, ofReal_im, one_re, one_im, add_zero]
  nlinarith

private theorem difference_le_of_error {κ δ E : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    {s : ℂ} (hs : 0 ≤ s.re)
    (hupper : (digamma (s / 2 + 1)).re - Real.log ‖s / 2 + 1‖ ≤ E)
    (hlower : -E ≤ (digamma ((s + (δ : ℂ)) / 2 + 1)).re -
      Real.log ‖(s + (δ : ℂ)) / 2 + 1‖) :
    smoothedGammaFactorDifference κ δ s ≤
      (1 - κ) / 2 * (Real.log ‖s / 2 + 1‖ - Real.log π) + (1 + κ) / 2 * E := by
  have hz : 0 < (s / 2 + 1).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
  have hlog := Real.log_le_log (hz.trans_le (re_le_norm _)) (gammaShift_norm_le hδ hs)
  have hlower' : Real.log ‖s / 2 + 1‖ - E ≤
      (digamma ((s + (δ : ℂ)) / 2 + 1)).re := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hlower' hκ
  unfold smoothedGammaFactorDifference
  nlinarith only [hupper, hscaled]

/-- The real-part error preserves the logarithmic coefficient on the right half-plane. -/
theorem smoothedGammaFactorDifference_le_log_norm {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    {s : ℂ} (hs : 0 ≤ s.re) :
    smoothedGammaFactorDifference κ δ s ≤
      (1 - κ) / 2 * (Real.log ‖s / 2 + 1‖ - Real.log π) + (1 + κ) / (s.re + 2) := by
  have hz : 0 < (s / 2 + 1).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
  have hwz : (s / 2 + 1).re ≤ ((s + (δ : ℂ)) / 2 + 1).re := by
    simp only [add_re, div_ofNat_re, one_re, ofReal_re]
    linarith
  have hw := hz.trans_le hwz
  have hi := one_div_le_one_div_of_le hz hwz
  have hu := (abs_le.mp (abs_re_digamma_sub_log_norm_le hz)).2
  have hl := (abs_le.mp (abs_re_digamma_sub_log_norm_le hw)).1
  have he := difference_le_of_error hκ hδ hs hu (by linarith)
  convert! he using 1
  simp only [add_re, div_ofNat_re, one_re]
  field_simp

/-- The norm-based error decays while preserving the same leading logarithm. -/
theorem smoothedGammaFactorDifference_le_log_norm_inv_norm {κ δ : ℝ}
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) {s : ℂ} (hs : 0 ≤ s.re) :
    smoothedGammaFactorDifference κ δ s ≤
      (1 - κ) / 2 * (Real.log ‖s / 2 + 1‖ - Real.log π) + (1 + κ) / ‖s / 2 + 1‖ := by
  have hz : 0 < (s / 2 + 1).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
  have hw : 0 < ((s + (δ : ℂ)) / 2 + 1).re := by
    simp only [add_re, div_ofNat_re, one_re, ofReal_re]
    linarith
  have hi : 2 / ‖(s + (δ : ℂ)) / 2 + 1‖ ≤ 2 / ‖s / 2 + 1‖ :=
    div_le_div_of_nonneg_left (by norm_num) (hz.trans_le (re_le_norm _))
      (gammaShift_norm_le hδ hs)
  have hu := (abs_le.mp (abs_re_digamma_sub_log_norm_le_inv_norm hz)).2
  have hl := (abs_le.mp (abs_re_digamma_sub_log_norm_le_inv_norm hw)).1
  have he := difference_le_of_error hκ hδ hs hu (by linarith)
  convert! he using 1
  ring

/-- At nonzero signed height the reciprocal-norm error is at most `2*(1+kappa)/abs(t)`. -/
theorem smoothedGammaFactorDifference_le_log_norm_height {κ δ : ℝ}
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) {s : ℂ} (hs : 0 ≤ s.re) (ht : s.im ≠ 0) :
    smoothedGammaFactorDifference κ δ s ≤
      (1 - κ) / 2 * (Real.log ‖s / 2 + 1‖ - Real.log π) + 2 * (1 + κ) / |s.im| := by
  apply (smoothedGammaFactorDifference_le_log_norm_inv_norm hκ hδ hs).trans
  apply add_le_add le_rfl
  have hn : |s.im| / 2 ≤ ‖s / 2 + 1‖ := by
    simpa [abs_div] using abs_im_le_norm (s / 2 + 1)
  have hd := div_le_div_of_nonneg_left (by linarith : 0 ≤ 1 + κ)
    (half_pos (abs_pos.mpr ht)) hn
  convert! hd using 1
  ring

end

end PrimeFactorUnimodality
