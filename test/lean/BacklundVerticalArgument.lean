import PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingEstimate

/-! # Euler logarithms and the vertical Backlund contour

Check the genuine exponential identity, the tight modulus and argument
bounds, signed and zero heights, and the actual counting estimate with
only its circle and regular-height hypotheses left explicit.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example {s : ℂ} (hs : 1 < s.re) :
    exp (riemannZetaEulerLog s) = riemannZeta s := exp_riemannZetaEulerLog hs

example {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZetaEulerLog s = logDeriv riemannZeta s := deriv_riemannZetaEulerLog hs

example {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZetaEulerLog s‖ ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ :=
  norm_riemannZetaEulerLog_le hs

example (σ : ℝ) : (riemannZetaEulerLog σ).im = 0 := riemannZetaEulerLog_ofReal_im σ

example {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta (s.re : ℂ)‖⁻¹ ≤ ‖riemannZeta s‖ := inv_norm_riemannZeta_real_le hs

example {s : ℂ} (hs : 1 < s.re) :
    exp (backlundRightLog s) = Backlund.zetaSurrogate s := exp_backlundRightLog hs

example {σ : ℝ} (hσ : 1 < σ) : (backlundRightLog (σ : ℂ)).im = 0 :=
  backlundRightLog_ofReal_im hσ

example {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T =
      backlundRightLog ((σ : ℂ) + T * I) - backlundRightLog (σ : ℂ) :=
  VIntegral_backlund_logDeriv_eq hσ T

example : |(VIntegral (logDeriv Backlund.zetaSurrogate) 2 0 (-3)).im| ≤
    Real.pi / 2 + Real.log ‖riemannZeta 2‖ := by
  exact abs_im_VIntegral_backlund_logDeriv_le (by norm_num : (1 : ℝ) < 2) (-3)

example : VIntegral (logDeriv Backlund.zetaSurrogate) 2 0 0 = 0 := by
  simpa using VIntegral_backlund_logDeriv_eq (by norm_num : (1 : ℝ) < 2) 0

example {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    |T| / ‖riemannZeta (σ : ℂ)‖ ≤ ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ :=
  abs_height_div_zeta_le_backlundSurrogate hσ T

example {σ T r R M : ℝ}
    (hσ : 1 < σ) (hT : 0 < T) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hseg : σ - 1 / 2 ≤ r)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0)
    (hp : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |Real.pi * riemannZeta.N T -
      ((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im)| ≤
      Real.pi / 2 + Real.log (1 / (σ - 1) + 1) + Real.pi *
        (Real.log (M * (1 / (σ - 1) + 1) / T) / Real.log (R / r)) :=
  abs_pi_mul_zeta_N_sub_gamma_le_pole hσ hT hr hrR hM hseg htop hp hm

end

end PrimeFactorUnimodality.Tests
