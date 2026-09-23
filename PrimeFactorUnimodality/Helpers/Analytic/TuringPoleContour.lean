import PrimeFactorUnimodality.Helpers.Analytic.BacklundVerticalArgument

/-! # Removing the zeta pole from the horizontal counting contour

At positive height the principal logarithm of `s-1` stays off its cut,
even as the real coordinate crosses one. Its exact increment separates
the surrogate contour into the zeta logarithmic derivative and the pole.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The pole primitive is continuous on an entire positive-height horizontal line. -/
theorem continuous_turingPoleLog {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : ℝ => log ((x : ℂ) + T * I - 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasDerivAt_log (Or.inr (by simpa using hT.ne'))).continuousAt.comp (by fun_prop)

/-- The pole reciprocal is integrable on every finite horizontal interval. -/
theorem intervalIntegrable_turingPole {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => 1 / ((x : ℂ) + T * I - 1)) volume a b := by
  apply Continuous.intervalIntegrable
  apply Continuous.div continuous_const (by fun_prop)
  intro x hx
  have hi := congrArg Complex.im hx
  simp only [sub_im, add_im, mul_im, ofReal_im, ofReal_re, I_im, I_re,
    one_im, zero_im, mul_one, mul_zero, add_zero, zero_add, sub_zero] at hi
  exact hT.ne' hi

/-- The exact pole contour increment, with its fixed principal-log branch. -/
theorem HIntegral_turingPole_eq {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    HIntegral (fun s => 1 / (s - 1)) a b T =
      log ((b : ℂ) + T * I - 1) - log ((a : ℂ) + T * I - 1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (intervalIntegrable_turingPole hT a b)
  intro x _
  have hs : (x : ℂ) + T * I - 1 ∈ slitPlane := Or.inr (by simpa using hT.ne')
  have hd := (hasDerivAt_log hs).comp (x : ℂ)
    (((hasDerivAt_id (x : ℂ)).add_const (T * I)).sub_const 1)
  simpa [one_div] using! hd.comp_ofReal

/-- Zeta's horizontal logarithmic derivative is integrable at every regular positive height. -/
theorem intervalIntegrable_turingZetaLogDeriv {σ T : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    IntervalIntegrable (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + T * I))
      volume (1 / 2) σ := by
  have hs := intervalIntegrable_backlundSurrogate_logDeriv hσ
    (fun x _ => backlund_surrogate_ne_zero_horizontal hT.ne' htop x)
  apply (hs.sub (intervalIntegrable_turingPole hT (1 / 2) σ)).congr
  intro x _
  have h1 : (x : ℂ) + T * I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hT.ne' hi
  have hz : riemannZeta ((x : ℂ) + T * I) ≠ 0 := fun hz =>
    htop _ (by simp) (riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero (by simpa using hT.ne') hz)
  simp only [logDeriv_backlundSurrogate_eq h1 hz]
  ring

/-- Separating the pole retains the left endpoint phase exactly. -/
theorem HIntegral_backlund_eq_pole_add_zeta {σ T : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) σ T =
      (log ((σ : ℂ) + T * I - 1) - log ((1 / 2 : ℂ) + T * I - 1)) +
        HIntegral (logDeriv riemannZeta) (1 / 2) σ T := by
  have hp := HIntegral_turingPole_eq hT (1 / 2) σ
  simp only [ofReal_div, ofReal_one, ofReal_ofNat] at hp
  rw [← hp]
  change (∫ x in (1 / 2 : ℝ)..σ, _) = (∫ x in (1 / 2 : ℝ)..σ, _) + ∫ x in (1 / 2 : ℝ)..σ, _
  rw [← intervalIntegral.integral_add (intervalIntegrable_turingPole hT (1 / 2) σ)
    (intervalIntegrable_turingZetaLogDeriv hσ hT htop)]
  apply intervalIntegral.integral_congr
  intro x _
  have h1 : (x : ℂ) + T * I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hT.ne' hi
  exact logDeriv_backlundSurrogate_eq h1 (fun hz => htop _ (by simp)
    (riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero (by simpa using hT.ne') hz))

end

end PrimeFactorUnimodality
