import PrimeFactorUnimodality.Helpers.Analytic.BacklundVerticalArgument
import PrimeFactorUnimodality.Helpers.Analytic.ZetaRealPole

/-! # The actual counting estimate with a controlled vertical argument and centre

Insert the proved uniform vertical argument bound and the Euler-product
centre lower bound into the actual half-contour identity and Jensen estimate.
The resulting bound contains only the gamma contour, circle norm bounds,
and elementary real parameters. Sharp gamma and circle estimates remain
necessary for the final numerical counting-error theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The centre lower bound gives an explicit upper bound for the Jensen logarithm. -/
theorem log_backlund_centre_ratio_le {σ T M : ℝ}
    (hσ : 1 < σ) (hT : 0 < T) (hM : 0 < M) :
    Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) ≤
      Real.log (M * ‖riemannZeta (σ : ℂ)‖ / T) := by
  have hZ : 0 < ‖riemannZeta (σ : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hσ.le)
  have hA : 0 < ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ :=
    norm_pos_iff.mpr (backlund_surrogate_ne_zero_of_one_lt_re (by simpa using hσ))
  have hc : T / ‖riemannZeta (σ : ℂ)‖ ≤
      ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ := by
    simpa only [abs_of_pos hT] using abs_height_div_zeta_le_backlundSurrogate hσ T
  apply Real.log_le_log (div_pos hM hA)
  calc
    _ ≤ M / (T / ‖riemannZeta (σ : ℂ)‖) :=
      div_le_div_of_nonneg_left hM.le (div_pos hT hZ) hc
    _ = _ := by rw [div_div_eq_mul_div]

/-- The actual zero count, with the vertical argument and Jensen centre fully estimated. -/
theorem abs_pi_mul_zeta_N_sub_gamma_le_euler {σ T r R M : ℝ}
    (hσ : 1 < σ) (hT : 0 < T) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hseg : σ - 1 / 2 ≤ r)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0)
    (hp : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |Real.pi * riemannZeta.N T -
      ((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im)| ≤
      Real.pi / 2 + Real.log ‖riemannZeta (σ : ℂ)‖ + Real.pi *
        (Real.log (M * ‖riemannZeta (σ : ℂ)‖ / T) / Real.log (R / r)) := by
  apply (abs_pi_mul_zeta_N_sub_gamma_le hσ hT hr hrR hM hseg htop hp hm).trans
  apply add_le_add (abs_im_VIntegral_backlund_logDeriv_le hσ T)
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  exact div_le_div_of_nonneg_right (log_backlund_centre_ratio_le hσ hT (by linarith))
    (Real.log_pos ((one_lt_div hr).mpr hrR)).le

/-- Abel's real-axis bound makes the remaining zeta value completely explicit. -/
theorem abs_pi_mul_zeta_N_sub_gamma_le_pole {σ T r R M : ℝ}
    (hσ : 1 < σ) (hT : 0 < T) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hseg : σ - 1 / 2 ≤ r)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0)
    (hp : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |Real.pi * riemannZeta.N T -
      ((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im)| ≤
      Real.pi / 2 + Real.log (1 / (σ - 1) + 1) + Real.pi *
        (Real.log (M * (1 / (σ - 1) + 1) / T) / Real.log (R / r)) := by
  have hZ : 0 < ‖riemannZeta (σ : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hσ.le)
  have hbound := norm_riemannZeta_real_le_pole_add_one hσ
  apply (abs_pi_mul_zeta_N_sub_gamma_le_euler hσ hT hr hrR hM hseg htop hp hm).trans
  apply add_le_add (add_le_add le_rfl (Real.log_le_log hZ hbound))
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  apply div_le_div_of_nonneg_right _ (Real.log_pos ((one_lt_div hr).mpr hrR)).le
  exact Real.log_le_log (div_pos (mul_pos (by linarith) hZ) hT)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (by linarith)) hT.le)

end

end PrimeFactorUnimodality
