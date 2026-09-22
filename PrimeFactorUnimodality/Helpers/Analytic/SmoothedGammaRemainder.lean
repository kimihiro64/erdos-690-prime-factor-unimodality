import PrimeFactorUnimodality.Helpers.Analytic.DigammaLowerBound
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Bounds
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Continuity
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrability.LogCauchy

set_option autoImplicit false

/-! # Absolute convergence of the smoothed gamma remainder

The integrand in Kadiri's `T₂` term pairs the real digamma function on the
quarter-line with the second-derivative Laplace transform divided by the
square of the displacement from the half-line. We prove continuity, an
explicit pointwise majorant, and absolute integrability for `Re(s) > 1/2`.
In particular, the domain includes the real parts below one needed by the
smoothed zero-free argument. This is not yet the explicit-formula identity.

The normalization is that of section 3.1 in Kadiri's
*Une région explicite sans zéros pour la fonction zeta de Riemann*.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The gamma remainder integrand before its factor `1 / (2π)`. -/
def smoothedGammaIntegrand (h : ℝ → ℂ) (d : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
    finiteLaplace h d (s - ((1 / 2 : ℂ) + (t : ℂ) * I)) /
      (s - ((1 / 2 : ℂ) + (t : ℂ) * I)) ^ 2

private theorem gamma_displacement_ne_zero {s : ℂ} (hs : 1 / 2 < s.re) (t : ℝ) :
    s - ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro heq
  have hre := congrArg Complex.re heq
  simp at hre
  linarith

private theorem gamma_displacement_norm_sq (s : ℂ) (t : ℝ) :
    ‖s - ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      (s.re - 1 / 2) ^ 2 + (t - s.im) ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]
  simp
  ring

/-- Continuity of the actual complex integrand, including measurability on the whole line. -/
theorem continuous_smoothedGammaIntegrand {h : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hh : ContinuousOn h (Icc 0 d)) {s : ℂ} (hs : 1 / 2 < s.re) :
    Continuous (smoothedGammaIntegrand h d s) := by
  have hψ : Continuous (fun t : ℝ => digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro t
    apply (Complex.continuousAt_digamma_of_re_pos (by norm_num)).comp
    fun_prop
  have hF : Continuous (fun t : ℝ => finiteLaplace h d
      (s - ((1 / 2 : ℂ) + (t : ℂ) * I))) := by
    simpa only [sub_sub] using continuous_finiteLaplace_vertical hd hh (s - 1 / 2)
  exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hψ)).mul hF).div
    (by fun_prop) (fun t => pow_ne_zero 2 (gamma_displacement_ne_zero hs t))

/-- Fully explicit pointwise bound, preserving the positive horizontal separation. -/
theorem norm_smoothedGammaIntegrand_le {h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M) (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {s : ℂ} (hs : 1 / 2 < s.re) (t : ℝ) :
    ‖smoothedGammaIntegrand h d s t‖ ≤
      (Real.log (|t| + 3) + |Real.eulerMascheroniConstant| + 5) *
        (M / (s.re - 1 / 2)) / ((s.re - 1 / 2) ^ 2 + (t - s.im) ^ 2) := by
  have hsep : 0 < (s - ((1 / 2 : ℂ) + (t : ℂ) * I)).re := by
    simp
    linarith
  have hF := norm_finiteLaplace_le_div_re hd hM hbound hsep
  simp only [sub_re, add_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re,
    ofReal_im, I_im, mul_zero, zero_mul, sub_zero, add_zero] at hF
  unfold smoothedGammaIntegrand
  rw [norm_div, norm_mul, norm_real, Real.norm_eq_abs, norm_pow,
    gamma_displacement_norm_sq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul (abs_re_digamma_quarter_line_le t) hF (norm_nonneg _)
    (by have := Real.log_nonneg (show 1 ≤ |t| + 3 by linarith [abs_nonneg t]); positivity)

/-- Absolute convergence of the gamma integral on the half-plane used in the paper. -/
theorem integrable_smoothedGammaIntegrand {h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hh : ContinuousOn h (Icc 0 d)) (hM : 0 ≤ M)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (smoothedGammaIntegrand h d s) := by
  let A : ℝ := |Real.eulerMascheroniConstant| + 5
  let K : ℝ := 1 + A / Real.log 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlog₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha : 0 < s.re - 1 / 2 := sub_pos.mpr hs
  have hkernel := Real.integrable_log_add_abs_div_cauchy ha (c := 3) (by norm_num) s.im
  have hmajor := hkernel.const_mul (K * (M / (s.re - 1 / 2)))
  apply hmajor.mono' (continuous_smoothedGammaIntegrand hd hh hs).aestronglyMeasurable
  filter_upwards with t
  have hlog : Real.log 3 ≤ Real.log (|t| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hcancel : A / Real.log 3 * Real.log 3 = A := div_mul_cancel₀ _ hlog₃.ne'
  have hconst : A ≤ A / Real.log 3 * Real.log (|t| + 3) := by
    calc A = A / Real.log 3 * Real.log 3 := hcancel.symm
         _ ≤ _ := mul_le_mul_of_nonneg_left hlog (div_nonneg hA hlog₃.le)
  have hweight : Real.log (|t| + 3) + |Real.eulerMascheroniConstant| + 5 ≤
      K * Real.log (|t| + 3) := by dsimp [K, A] at *; nlinarith
  calc
    _ ≤ (Real.log (|t| + 3) + |Real.eulerMascheroniConstant| + 5) *
        (M / (s.re - 1 / 2)) / ((s.re - 1 / 2) ^ 2 + (t - s.im) ^ 2) :=
      norm_smoothedGammaIntegrand_le hd hM hbound hs t
    _ ≤ (K * Real.log (|t| + 3)) * (M / (s.re - 1 / 2)) /
        ((s.re - 1 / 2) ^ 2 + (t - s.im) ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hweight (div_nonneg hM ha.le))
        (by positivity)
    _ = _ := by ring

end

end PrimeFactorUnimodality
