import PrimeFactorUnimodality.Helpers.Analytic.DigammaLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # Explicit shifted Gamma-factor bounds with the correct leading coefficient

Both sides of the digamma logarithmic approximation are used. A positive
real shift increases the norm and decreases the reciprocal-real-part error,
so subtraction retains the factor `1-kappa` on the leading logarithm.
No logarithmic lower bound or unspecified asymptotic constant is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The shifted difference preserves its logarithmic coefficient on the right half-plane. -/
theorem smoothedGammaFactorDifference_le_log_norm {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    {s : ℂ} (hs : 0 ≤ s.re) :
    smoothedGammaFactorDifference κ δ s ≤
      (1 - κ) / 2 * (Real.log ‖s / 2 + 1‖ - Real.log π) + (1 + κ) / (s.re + 2) := by
  let z := s / 2 + 1
  let w := (s + (δ : ℂ)) / 2 + 1
  have hz : 0 < z.re := by
    simp only [z, add_re, div_ofNat_re, one_re]
    linarith
  have hwz : z.re ≤ w.re := by
    simp only [z, w, add_re, div_ofNat_re, one_re, ofReal_re]
    linarith
  have hw : 0 < w.re := hz.trans_le hwz
  have him : z.im = w.im := by simp [z, w]
  have hnorm : ‖z‖ ≤ ‖w‖ := by
    apply (sq_le_sq₀ (norm_nonneg z) (norm_nonneg w)).mp
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply, him]
    nlinarith
  have hlog := Real.log_le_log (norm_pos_iff.mpr (by
    intro he
    simp [he] at hz : z ≠ 0)) hnorm
  have hupper := (abs_le.mp (abs_re_digamma_sub_log_norm_le hz)).2
  have hlower := (abs_le.mp (abs_re_digamma_sub_log_norm_le hw)).1
  have hi : 1 / w.re ≤ 1 / z.re := one_div_le_one_div_of_le hz hwz
  have hlower' : Real.log ‖z‖ - 1 / z.re ≤ (digamma w).re := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hlower' hκ
  have herr : (1 + κ) / (s.re + 2) = (1 + κ) / 2 * (1 / z.re) := by
    simp only [z, add_re, div_ofNat_re, one_re]
    field_simp
  rw [herr]
  change _ ≤ (1 - κ) / 2 * (Real.log ‖z‖ - Real.log π) + _
  unfold smoothedGammaFactorDifference
  change (-(1 / 2 : ℝ) * Real.log π + (1 / 2 : ℝ) * (digamma z).re) -
    κ * (-(1 / 2 : ℝ) * Real.log π + (1 / 2 : ℝ) * (digamma w).re) ≤ _
  nlinarith only [hupper, hscaled]

/-- An elementary height majorant for the actual Gamma factor in the working strip. -/
def smoothedGammaFactorMajorant (κ σ t : ℝ) : ℝ :=
  (1 - κ) / 2 * (Real.log (|t| / 2 + 2) - Real.log π) + (1 + κ) / (σ + 2)

/-- The vertical strip bound includes all signed and zero heights. -/
theorem smoothedGammaFactorDifference_le_majorant {κ δ : ℝ}
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ) {s : ℂ}
    (hs : 0 ≤ s.re) (hs₂ : s.re ≤ 2) :
    smoothedGammaFactorDifference κ δ s ≤ smoothedGammaFactorMajorant κ s.re s.im := by
  apply (smoothedGammaFactorDifference_le_log_norm hκ hδ hs).trans
  have hz : 0 < (s / 2 + 1).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
  have hn := norm_le_abs_re_add_abs_im (s / 2 + 1)
  rw [abs_of_pos hz] at hn
  simp only [add_re, div_ofNat_re, one_re, add_im, div_ofNat_im, one_im, add_zero, abs_div] at hn
  norm_num at hn
  have hlog : Real.log ‖s / 2 + 1‖ ≤ Real.log (|s.im| / 2 + 2) :=
    Real.log_le_log (norm_pos_iff.mpr (by intro he; simp [he] at hz)) (by linarith)
  have h := mul_le_mul_of_nonneg_left (sub_le_sub_right hlog (Real.log π))
    (by positivity : 0 ≤ (1 - κ) / 2)
  exact add_le_add h le_rfl

/-- Nonnegative polynomial coefficients preserve the explicit Gamma-factor majorant. -/
theorem sum_smoothedGammaFactorDifference_le {κ δ σ : ℝ}
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hσ₂ : σ ≤ 2)
    {ι : Type*} (S : Finset ι) (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (t : ℝ) :
    (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ ((σ : ℂ) + (k i * t : ℝ) * I)) ≤
      ∑ i ∈ S, a i * smoothedGammaFactorMajorant κ σ (k i * t) := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (ha i hi)
  simpa using smoothedGammaFactorDifference_le_majorant hκ hκ₁ hδ
    (s := (σ : ℂ) + (k i * t : ℝ) * I) (by simpa using hσ) (by simpa using hσ₂)

end

end PrimeFactorUnimodality
