import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaNormBounds
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaRealBounds

/-! # Explicit shifted Gamma-factor bounds with the correct leading coefficient

Take the better of the two proved Gamma errors at nonzero height and the
one-sided real digamma bound at zero. Subtraction retains `1-kappa` on the leading
logarithm. The height-decaying improvement is used by the actual master,
not merely supplied as a separate estimate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The one-sided bound at zero and the smaller of the two norm errors elsewhere. -/
def smoothedGammaFactorError (κ σ t : ℝ) : ℝ :=
  if t = 0 then κ / (σ + 2)
  else min ((1 + κ) / (σ + 2)) (2 * (1 + κ) / |t|)

/-- Zero height never uses the reciprocal-height estimate. -/
@[simp] theorem smoothedGammaFactorError_zero (κ σ : ℝ) :
    smoothedGammaFactorError κ σ 0 = κ / (σ + 2) := by
  simp [smoothedGammaFactorError]

/-- The improved error never exceeds the previous real-part bound. -/
theorem smoothedGammaFactorError_le_re (κ σ t : ℝ) (hσ : -2 ≤ σ) :
    smoothedGammaFactorError κ σ t ≤ (1 + κ) / (σ + 2) := by
  unfold smoothedGammaFactorError
  split_ifs
  · exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · exact min_le_left _ _

/-- At every nonzero signed height the error has explicit reciprocal decay. -/
theorem smoothedGammaFactorError_le_height (κ σ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    smoothedGammaFactorError κ σ t ≤ 2 * (1 + κ) / |t| := by
  simp only [smoothedGammaFactorError, ht, ↓reduceIte]
  exact min_le_right _ _

/-- The error at each natural harmonic decreases with positive base height. -/
theorem antitoneOn_smoothedGammaFactorError_nat {κ : ℝ} (hκ : 0 ≤ κ)
    (σ : ℝ) (i : ℕ) :
    AntitoneOn (fun t => smoothedGammaFactorError κ σ ((i : ℝ) * t)) (Set.Ioi 0) := by
  intro t ht u hu htu
  by_cases hi : i = 0
  · simp [hi]
  have hi₀ : (0 : ℝ) < i := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)
  have ht₀ : 0 < (i : ℝ) * t := mul_pos hi₀ ht
  have hu₀ : 0 < (i : ℝ) * u := mul_pos hi₀ hu
  simp only [smoothedGammaFactorError, ht₀.ne', hu₀.ne', ↓reduceIte,
    abs_of_pos ht₀, abs_of_pos hu₀]
  exact min_le_min le_rfl (div_le_div_of_nonneg_left (by positivity) ht₀
    (mul_le_mul_of_nonneg_left htu hi₀.le))

/-- An elementary height majorant for the actual Gamma factor in the working strip. -/
def smoothedGammaFactorMajorant (κ σ t : ℝ) : ℝ :=
  (1 - κ) / 2 * (Real.log (|t| / 2 + 2) - Real.log π) + smoothedGammaFactorError κ σ t

/-- The error decreases with the real coordinate wherever its real-part denominator is positive. -/
theorem antitoneOn_smoothedGammaFactorError_sigma {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) :
    AntitoneOn (fun σ => smoothedGammaFactorError κ σ t) (Set.Ioi (-2)) := by
  intro σ hσ τ hτ hστ
  have hσpos : -2 < σ := hσ
  have he : (1 + κ) / (τ + 2) ≤ (1 + κ) / (σ + 2) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith : 0 < σ + 2)
      (by linarith)
  unfold smoothedGammaFactorError
  split_ifs
  · exact div_le_div_of_nonneg_left hκ (by linarith : 0 < σ + 2) (by linarith)
  · exact min_le_min he le_rfl

/-- The vertical strip bound includes all signed and zero heights. -/
theorem smoothedGammaFactorDifference_le_majorant {κ δ : ℝ}
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ) {s : ℂ}
    (hs : 0 ≤ s.re) (hs₂ : s.re ≤ 2) :
    smoothedGammaFactorDifference κ δ s ≤ smoothedGammaFactorMajorant κ s.re s.im := by
  have hbound : smoothedGammaFactorDifference κ δ s ≤
      (1 - κ) / 2 * (Real.log ‖s / 2 + 1‖ - Real.log π) +
        smoothedGammaFactorError κ s.re s.im := by
    have hr := smoothedGammaFactorDifference_le_log_norm hκ hδ hs
    by_cases ht : s.im = 0
    · have hsreal : s = (s.re : ℂ) := Complex.ext (by simp) (by simpa using ht)
      have hb := smoothedGammaFactorDifference_ofReal_le hκ hδ hs
      rw [hsreal]
      simpa only [ofReal_re, ofReal_im, smoothedGammaFactorError_zero,
        ← ofReal_ofNat, ← ofReal_div, ← ofReal_one, ← ofReal_add, norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < s.re / 2 + 1)] using hb
    · have hh := smoothedGammaFactorDifference_le_log_norm_height hκ hδ hs ht
      simp only [smoothedGammaFactorError, ht, ↓reduceIte, add_min]
      exact le_min hr hh
  apply hbound.trans
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
