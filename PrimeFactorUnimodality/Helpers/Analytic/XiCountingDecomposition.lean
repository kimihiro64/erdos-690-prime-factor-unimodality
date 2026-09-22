import PrimeFactorUnimodality.Helpers.Analytic.BacklundArgumentIntegral
import PrimeFactorUnimodality.Helpers.Analytic.BacklundXiLogDerivative
import PrimeFactorUnimodality.Helpers.Analytic.XiHalfContour
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-! # Separating the actual counting contour into surrogate and gamma integrals

The pointwise xi product identity is integrated on both half-contour segments.
Continuity and nonvanishing establish integrability before splitting either
integral. This leaves the gamma contribution explicit and connects the actual
zero count to the proved horizontal Backlund estimate. No quantitative bound
on the gamma contribution is assumed or asserted here.

Digamma continuity is reused from Robby Sneiderman's Apache-2.0 PNT module
`DigammaSeries`, revision `f6147e7572ab3abe5428101bc0b13627bcb005df`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The gamma and pi terms in the shifted xi product's logarithmic derivative. -/
def xiGammaLogDerivative (s : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * Real.log Real.pi + (1 / 2 : ℂ) * digamma (s / 2 + 1)

/-- The shifted gamma contribution is continuous on the right half-plane. -/
theorem continuousAt_xiGammaLogDerivative {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt xiGammaLogDerivative s := by
  have hg : 0 < (s / 2 + 1).re := by
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  exact continuousAt_const.add (continuousAt_const.mul
    ((continuousAt_digamma_of_re_pos hg).comp (f := fun z : ℂ => z / 2 + 1)
      (show ContinuousAt (fun z : ℂ => z / 2 + 1) s by fun_prop)))

/-- Every vertical line to the right of the critical strip avoids surrogate zeros. -/
theorem continuous_backlund_logDeriv_vertical {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun t : ℝ => logDeriv Backlund.zetaSurrogate ((σ : ℂ) + t * I)) := by
  have hdc : Continuous (deriv Backlund.zetaSurrogate) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (Backlund.zetaSurrogate_differentiable.analyticAt z).deriv.continuousAt)
  have hc : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
  exact (hdc.comp hc).div (Backlund.zetaSurrogate_differentiable.continuous.comp hc)
    (fun t => backlund_surrogate_ne_zero_of_one_lt_re (by simpa))

/-- The gamma integrand is continuous along every positive-real-part vertical line. -/
theorem continuous_xiGammaLogDerivative_vertical {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun t : ℝ => xiGammaLogDerivative ((σ : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (continuousAt_xiGammaLogDerivative (by simpa using hσ)).comp (by fun_prop)

/-- The gamma integrand is integrable on horizontal segments in the right half-plane. -/
theorem intervalIntegrable_xiGammaLogDerivative_horizontal {a b T : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => xiGammaLogDerivative ((x : ℂ) + T * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  apply ContinuousAt.continuousWithinAt
  exact (continuousAt_xiGammaLogDerivative (by simpa using ha.trans_le hx.1)).comp
    (by fun_prop)

/-- A nonreal horizontal line avoiding xi zeros also avoids surrogate zeros. -/
theorem backlund_surrogate_ne_zero_horizontal {T : ℝ} (hT : T ≠ 0)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) (x : ℝ) :
    Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0 := by
  have hi : ((x : ℂ) + T * I).im ≠ 0 := by simpa using hT
  have hs1 : (x : ℂ) + T * I ≠ 1 := by
    intro h
    exact hi (by simp [h])
  have hζ : riemannZeta ((x : ℂ) + T * I) ≠ 0 := fun hz =>
    htop _ (by simp) (riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero hi hz)
  simp only [Backlund.zetaSurrogate, ite_eq_right hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) hζ

/-- The right vertical xi integral splits into two genuinely integrable contributions. -/
theorem VIntegral_logDeriv_xi_decomposition {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    VIntegral (logDeriv riemannXi) σ 0 T =
      VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T +
        VIntegral xiGammaLogDerivative σ 0 T := by
  have he (t : ℝ) : logDeriv riemannXi ((σ : ℂ) + t * I) =
      logDeriv Backlund.zetaSurrogate ((σ : ℂ) + t * I) +
        xiGammaLogDerivative ((σ : ℂ) + t * I) := by
    have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
    have hs1 : (σ : ℂ) + t * I ≠ 1 := by intro h; simp [h] at hs
    rw [logDeriv_xi_eq_backlundSurrogate (by linarith) hs1
      (riemannZeta_ne_zero_of_one_le_re hs.le), xiGammaLogDerivative]
    ring
  unfold VIntegral
  simp only [he]
  rw [intervalIntegral.integral_add
    ((continuous_backlund_logDeriv_vertical hσ).intervalIntegrable 0 T)
    ((continuous_xiGammaLogDerivative_vertical (by linarith : 0 < σ)).intervalIntegrable 0 T)]
  exact smul_add _ _ _

/-- The top-right xi integral splits without introducing a principal-log branch. -/
theorem HIntegral_logDeriv_xi_decomposition {σ T : ℝ} (hσ : 1 ≤ σ) (hT : T ≠ 0)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HIntegral (logDeriv riemannXi) (1 / 2) σ T =
      HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) σ T +
        HIntegral xiGammaLogDerivative (1 / 2) σ T := by
  have hab : (1 / 2 : ℝ) ≤ σ := by linarith
  have he : HIntegral (logDeriv riemannXi) (1 / 2) σ T =
      ∫ x in (1 / 2 : ℝ)..σ, (logDeriv Backlund.zetaSurrogate ((x : ℂ) + T * I) +
        xiGammaLogDerivative ((x : ℂ) + T * I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hs : 0 < ((x : ℂ) + T * I).re := by simp; linarith [hx.1]
    have hi : ((x : ℂ) + T * I).im ≠ 0 := by simpa using hT
    have hs1 : (x : ℂ) + T * I ≠ 1 := by intro h; exact hi (by simp [h])
    have hζ : riemannZeta ((x : ℂ) + T * I) ≠ 0 := fun hz =>
      htop _ (by simp) (riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero hi hz)
    dsimp only
    rw [logDeriv_xi_eq_backlundSurrogate hs hs1 hζ, xiGammaLogDerivative]
    ring
  rw [he]
  exact intervalIntegral.integral_add
    (intervalIntegrable_backlundSurrogate_logDeriv hab
      (fun x _ => backlund_surrogate_ne_zero_horizontal hT htop x))
    (intervalIntegrable_xiGammaLogDerivative_horizontal (by norm_num) hab)

/-- The actual count separates into its surrogate argument and gamma contributions. -/
theorem pi_mul_zeta_N_eq_surrogate_gamma_contour {σ T : ℝ} (hσ : 1 < σ) (hT : 0 < T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Real.pi * riemannZeta.N T =
      ((VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T).im -
        (HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) σ T).im) +
      ((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im) := by
  rw [pi_mul_zeta_N_eq_xi_half_contour hσ.le hT.le htop,
    VIntegral_logDeriv_xi_decomposition hσ,
    HIntegral_logDeriv_xi_decomposition hσ.le hT.ne' htop, add_im, add_im]
  ring

/-- The proved Jensen estimate controls the actual count after gamma separation.
The vertical surrogate term and the explicit circle bounds remain to be estimated. -/
theorem abs_pi_mul_zeta_N_sub_gamma_le {σ T r R M : ℝ}
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
          Real.log (R / r)) := by
  have hb := abs_im_integral_backlundSurrogate_logDeriv_le
    hσ hr hrR hM (show (1 / 2 : ℝ) ≤ σ by linarith)
    (fun x hx => by rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]; linarith [hx.1])
    (fun x _ => backlund_surrogate_ne_zero_horizontal hT.ne' htop x) hp hm
  rw [pi_mul_zeta_N_eq_surrogate_gamma_contour hσ hT htop, add_sub_cancel_right]
  exact (abs_sub _ _).trans (add_le_add le_rfl hb)

end

end PrimeFactorUnimodality
