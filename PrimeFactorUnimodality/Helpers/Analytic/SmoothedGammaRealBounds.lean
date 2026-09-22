import PrimeFactorUnimodality.Helpers.Analytic.DigammaRealBounds
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # The improved zero-height Gamma factor

At a real argument, the first digamma has no upper logarithmic error.
Only the lower error at the shifted argument remains, with coefficient
`kappa` instead of `1+kappa`. This applies for every nonnegative shift.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The real-axis shifted difference needs only the lower digamma error. -/
theorem smoothedGammaFactorDifference_ofReal_le {κ δ σ : ℝ}
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) :
    smoothedGammaFactorDifference κ δ (σ : ℂ) ≤
      (1 - κ) / 2 * (Real.log (σ / 2 + 1) - Real.log π) + κ / (σ + 2) := by
  have hx : 0 < σ / 2 + 1 := by linarith
  have hy : 0 < (σ + δ) / 2 + 1 := by linarith
  have hxy : σ / 2 + 1 ≤ (σ + δ) / 2 + 1 := by linarith
  have hu := re_digamma_ofReal_le_log hx
  have hl := (abs_le.mp (abs_re_digamma_sub_log_norm_le
    (z := (((σ + δ) / 2 + 1 : ℝ) : ℂ)) hy)).1
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos hy, ofReal_re] at hl
  have hlog := Real.log_le_log hx hxy
  have hi := one_div_le_one_div_of_le hx hxy
  have hlow : Real.log (σ / 2 + 1) - 1 / (σ / 2 + 1) ≤
      (digamma (((σ + δ) / 2 + 1 : ℝ) : ℂ)).re := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hlow hκ
  have hid : κ / (σ + 2) = κ / 2 * (1 / (σ / 2 + 1)) := by
    field_simp
  unfold smoothedGammaFactorDifference
  push_cast at hu hscaled
  rw [hid]
  nlinarith only [hu, hscaled]

end

end PrimeFactorUnimodality
