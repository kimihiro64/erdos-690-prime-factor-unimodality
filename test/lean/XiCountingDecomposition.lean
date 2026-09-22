import PrimeFactorUnimodality.Helpers.Analytic.XiCountingDecomposition

/-! # The surrogate and gamma integrals in the actual zero count

Check the genuine integral splitting, including the zero-height vertical
segment, horizontal orientation, and the transfer of the Jensen bound to
the actual multiplicity-weighted count. Circle norm hypotheses remain explicit.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example : Continuous (fun t : ℝ => xiGammaLogDerivative (2 + t * I)) := by
  exact continuous_xiGammaLogDerivative_vertical (by norm_num : (0 : ℝ) < 2)

example {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    VIntegral (logDeriv riemannXi) σ 0 T =
      VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T +
        VIntegral xiGammaLogDerivative σ 0 T :=
  VIntegral_logDeriv_xi_decomposition hσ T

example : VIntegral (logDeriv riemannXi) 2 0 0 =
    VIntegral (logDeriv Backlund.zetaSurrogate) 2 0 0 +
      VIntegral xiGammaLogDerivative 2 0 0 :=
  VIntegral_logDeriv_xi_decomposition (by norm_num) 0

example {T : ℝ} (hT : T ≠ 0)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) (x : ℝ) :
    Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0 :=
  backlund_surrogate_ne_zero_horizontal hT htop x

example {T : ℝ} (hT : T ≠ 0)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HIntegral (logDeriv riemannXi) (1 / 2) 1 T =
      HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) 1 T +
        HIntegral xiGammaLogDerivative (1 / 2) 1 T :=
  HIntegral_logDeriv_xi_decomposition le_rfl hT htop

example {σ T : ℝ} (hσ : 1 < σ) (hT : 0 < T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Real.pi * riemannZeta.N T =
      ((VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T).im -
        (HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) σ T).im) +
      ((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im) :=
  pi_mul_zeta_N_eq_surrogate_gamma_contour hσ hT htop

example {σ T r R M : ℝ}
    (hσ : 1 < σ) (hT : 0 < T) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hseg : σ - 1 / 2 ≤ r)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0)
    (hp : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |Real.pi * riemannZeta.N T -
      ((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im)| ≤
      |(VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T).im| + Real.pi *
        (Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) /
          Real.log (R / r)) :=
  abs_pi_mul_zeta_N_sub_gamma_le hσ hT hr hrR hM hseg htop hp hm

end

end PrimeFactorUnimodality.Tests
