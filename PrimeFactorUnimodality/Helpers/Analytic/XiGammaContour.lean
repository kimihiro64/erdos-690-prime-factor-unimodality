import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingPhase
import PrimeFactorUnimodality.Helpers.Analytic.XiCountingDecomposition

/-! # The exact gamma contribution to the half-counting contour

A fixed analytic Gamma logarithm is a primitive of the actual contour
integrand. The corner terms cancel, and the real starting point contributes
no phase. The remaining endpoint has real part `5/4`, so the proved
Stirling phase error is at most `1/10`, independently of the height.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The analytic primitive of the gamma and pi terms in the xi product. -/
def xiGammaLog (s : ℂ) : ℂ :=
  gammaRightLog (s / 2 + 1) - s / 2 * Real.log Real.pi

/-- Differentiating the actual branch recovers the separated gamma integrand. -/
theorem hasDerivAt_xiGammaLog {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt xiGammaLog (xiGammaLogDerivative s) s := by
  have hg : 0 < (s / 2 + 1).re := by simp; linarith
  have hd := ((hasDerivAt_gammaRightLog hg).comp s
    (((hasDerivAt_id s).div_const 2).add_const 1)).sub
      (((hasDerivAt_id s).div_const 2).mul_const (Real.log Real.pi : ℂ))
  convert! hd using 1
  dsimp [xiGammaLogDerivative]
  ring

/-- At a positive real point the primitive has zero imaginary part. -/
theorem xiGammaLog_ofReal_im {σ : ℝ} (hσ : 0 < σ) :
    (xiGammaLog (σ : ℂ)).im = 0 := by
  have he : (σ : ℂ) / 2 + 1 = ((σ / 2 + 1 : ℝ) : ℂ) := by push_cast; rfl
  simp only [xiGammaLog, he, sub_im, mul_im, ofReal_im, div_ofNat_im,
    zero_div, mul_zero, zero_mul, add_zero, sub_zero]
  exact gammaRightLog_ofReal_im (by positivity)

/-- The vertical gamma integral is an exact logarithmic increment, at every real height. -/
theorem VIntegral_xiGammaLogDerivative_eq {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    VIntegral xiGammaLogDerivative σ 0 T =
      xiGammaLog ((σ : ℂ) + T * I) - xiGammaLog (σ : ℂ) := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => xiGammaLog ((σ : ℂ) + y * I))
      (I * xiGammaLogDerivative ((σ : ℂ) + t * I)) t := by
    have h := (hasDerivAt_xiGammaLog (by simpa using hσ)).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const I).const_add (σ : ℂ))
    simpa [mul_comm] using! h.comp_ofReal
  have hi := ((continuous_xiGammaLogDerivative_vertical hσ).intervalIntegrable
    (μ := volume) 0 T).const_mul I
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [intervalIntegral.integral_const_mul, ofReal_zero, zero_mul, add_zero,
    VIntegral, smul_eq_mul] using h

/-- The horizontal gamma integral uses the same branch, so its corner cancels exactly. -/
theorem HIntegral_xiGammaLogDerivative_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (T : ℝ) :
    HIntegral xiGammaLogDerivative a b T =
      xiGammaLog ((b : ℂ) + T * I) - xiGammaLog ((a : ℂ) + T * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
    (intervalIntegrable_xiGammaLogDerivative_horizontal ha hab)
  intro x hx
  have hx' : a ≤ x := (uIcc_of_le hab ▸ hx).1
  have hs : 0 < ((x : ℂ) + T * I).re := by simpa using ha.trans_le hx'
  have h := (hasDerivAt_xiGammaLog hs).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).add_const (T * I))
  simpa using! h.comp_ofReal

/-- The half-contour gamma phase is just the fixed left endpoint phase. -/
theorem xiGamma_half_contour_eq {σ : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ) (T : ℝ) :
    (VIntegral xiGammaLogDerivative σ 0 T).im -
      (HIntegral xiGammaLogDerivative (1 / 2) σ T).im =
      (gammaRightLog ((5 / 4 : ℂ) + (T : ℂ) / 2 * I)).im - T / 2 * Real.log Real.pi := by
  rw [VIntegral_xiGammaLogDerivative_eq (by linarith : 0 < σ),
    HIntegral_xiGammaLogDerivative_eq (by norm_num) hσ, sub_im, sub_im,
    xiGammaLog_ofReal_im (by linarith : 0 < σ)]
  have he : (((1 / 2 : ℝ) : ℂ) + T * I) / 2 + 1 =
      (5 / 4 : ℂ) + (T : ℂ) / 2 * I := by push_cast; ring
  simp only [xiGammaLog, he, sub_im, mul_im, div_ofNat_im, add_im,
    ofReal_im, zero_add, ofReal_re, I_re, I_im, mul_zero, mul_one, add_zero]
  ring

/-- The exact gamma half-contour differs from the explicit Stirling phase by at most `1/10`. -/
theorem abs_xiGamma_half_contour_sub_stirling_le {σ : ℝ}
    (hσ : (1 / 2 : ℝ) ≤ σ) (T : ℝ) :
    |((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im) -
      ((3 / 4 : ℝ) * arg ((5 / 4 : ℂ) + (T : ℂ) / 2 * I) +
        T / 2 * Real.log ‖(5 / 4 : ℂ) + (T : ℂ) / 2 * I‖ -
          T / 2 - T / 2 * Real.log Real.pi)| ≤ 1 / 10 := by
  rw [xiGamma_half_contour_eq hσ]
  have h := abs_gammaRightLog_im_sub_explicit_le
    (z := (5 / 4 : ℂ) + (T : ℂ) / 2 * I) (by norm_num)
  norm_num [add_re, add_im, mul_re, mul_im, div_ofNat_re, div_ofNat_im] at h
  convert h using 1
  congr 1
  ring

/-- The gamma contour has an absolute constant error from the zero-counting main term. -/
theorem abs_xiGamma_half_contour_sub_mainTerm_le {σ T : ℝ}
    (hσ : (1 / 2 : ℝ) ≤ σ) (hT : 0 < T) :
    |((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im) -
      (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)| ≤
      3 * Real.pi / 8 + 27 / 20 := by
  let z : ℂ := (5 / 4 : ℂ) + (T : ℂ) / 2 * I
  have hzre : z.re = 5 / 4 := by dsimp [z]; norm_num
  have hzim : z.im = T / 2 := by dsimp [z]; simp
  have ht : 0 < T / 2 := by positivity
  have hn : T / 2 ≤ ‖z‖ := by simpa only [hzim] using im_le_norm z
  have hn0 : 0 < ‖z‖ := ht.trans_le hn
  have hnup : ‖z‖ ≤ 5 / 4 + T / 2 := by
    simpa only [hzre, hzim, abs_of_pos ht, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
      using norm_le_abs_re_add_abs_im z
  have hd0 : 0 ≤ Real.log ‖z‖ - Real.log (T / 2) :=
    sub_nonneg.mpr (Real.log_le_log ht hn)
  have hd : T / 2 * (Real.log ‖z‖ - Real.log (T / 2)) ≤ 5 / 4 := by
    have hl := Real.log_le_sub_one_of_pos (div_pos hn0 ht)
    rw [Real.log_div hn0.ne' ht.ne'] at hl
    have hm := mul_le_mul_of_nonneg_left hl ht.le
    have he : T / 2 * (‖z‖ / (T / 2) - 1) = ‖z‖ - T / 2 := by field_simp
    rw [he] at hm
    linarith
  have ha : |(3 / 4 : ℝ) * arg z| ≤ 3 * Real.pi / 8 := by
    have hb := (abs_arg_le_pi_div_two_iff.mpr (by rw [hzre]; norm_num) :
      |arg z| ≤ Real.pi / 2)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    linarith
  have he : (3 / 4 : ℝ) * arg z + T / 2 * Real.log ‖z‖ -
      T / 2 - T / 2 * Real.log Real.pi -
        (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2) =
      (3 / 4 : ℝ) * arg z + T / 2 * (Real.log ‖z‖ - Real.log (T / 2)) := by
    rw [show T / (2 * Real.pi) = (T / 2) / Real.pi by ring,
      Real.log_div ht.ne' Real.pi_pos.ne']
    ring
  have herr : |(3 / 4 : ℝ) * arg z + T / 2 * Real.log ‖z‖ -
      T / 2 - T / 2 * Real.log Real.pi -
        (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)| ≤
        3 * Real.pi / 8 + 5 / 4 := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add ha
      (by rwa [abs_of_nonneg (mul_nonneg ht.le hd0)]))
  have h := abs_xiGamma_half_contour_sub_stirling_le hσ T
  have htriangle := abs_sub_le
    ((VIntegral xiGammaLogDerivative σ 0 T).im -
      (HIntegral xiGammaLogDerivative (1 / 2) σ T).im)
    ((3 / 4 : ℝ) * arg z + T / 2 * Real.log ‖z‖ - T / 2 - T / 2 * Real.log Real.pi)
    (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)
  linarith

end

end PrimeFactorUnimodality
