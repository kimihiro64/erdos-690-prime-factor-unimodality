import PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingEstimate
import PrimeFactorUnimodality.Helpers.Analytic.XiGammaContour
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingRemainder

/-! # Actual zero-counting error with the gamma contribution discharged

Combine the proved uniform Stirling phase error, vertical Euler logarithm,
and horizontal Jensen estimate. The remaining analytic input is the
explicit circle norm bound; no gamma, counting, or phase estimate is
assumed. The result is at regular heights, with the existing regular-height
transfer available for the multiplicity-counted closed endpoint convention.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The actual counting discrepancy is bounded solely in terms of circle parameters. -/
theorem abs_zeta_N_sub_mainTerm_le_circle {σ T r R M : ℝ}
    (hσ : 1 < σ) (hT : 0 < T) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hseg : σ - 1 / 2 ≤ r)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0)
    (hp : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |riemannZeta.N T - xiZeroCountingMainTerm T| ≤
      7 / 8 + 27 / (20 * Real.pi) + Real.log (1 / (σ - 1) + 1) / Real.pi +
        Real.log (M * (1 / (σ - 1) + 1) / T) / Real.log (R / r) := by
  have hb := abs_pi_mul_zeta_N_sub_gamma_le_pole hσ hT hr hrR hM hseg htop hp hm
  have hg := abs_xiGamma_half_contour_sub_mainTerm_le (by linarith : (1 / 2 : ℝ) ≤ σ) hT
  have hn := (abs_sub_le (Real.pi * riemannZeta.N T)
    ((VIntegral xiGammaLogDerivative σ 0 T).im -
      (HIntegral xiGammaLogDerivative (1 / 2) σ T).im)
    (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)).trans (add_le_add hb hg)
  have he : Real.pi * (riemannZeta.N T - xiZeroCountingMainTerm T) =
      Real.pi * riemannZeta.N T - (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2) := by
    unfold xiZeroCountingMainTerm
    field_simp
  apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
  calc
    _ = |Real.pi * riemannZeta.N T - (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)| := by
      rw [← he, abs_mul, abs_of_pos Real.pi_pos, mul_comm]
    _ ≤ _ := hn
    _ = _ := by field_simp; ring

end

end PrimeFactorUnimodality
