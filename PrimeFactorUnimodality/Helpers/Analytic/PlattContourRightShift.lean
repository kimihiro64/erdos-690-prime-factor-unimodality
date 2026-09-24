import PrimeFactorUnimodality.Helpers.Analytic.PlattContourEdgeBound
import PrimeFactorUnimodality.Helpers.Analytic.PlattShiftedGammaIntegral
import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowFourier
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.HorizontalIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.PolynomialDecay

set_option autoImplicit false

/-! # The rightward contour shift for the actual Gamma-window Fourier transform

Both connecting edges vanish by a uniform polynomial-Gaussian bound. The
integrand is holomorphic throughout the intervening strip, so Cauchy-Goursat
identifies the actual Fourier transform with the displaced integral. Combining
this identity with the earlier integral estimate gives positive-frequency decay.
The negative-frequency contour crosses poles and is not asserted here.
-/

open MeasureTheory Filter Set
open scoped Topology FourierTransform

namespace PrimeFactorUnimodality

/-- The downward half-plane contains no Gamma pole of this integrand. -/
theorem differentiableAt_plattContourIntegrand_of_im_nonpos (k : ℕ) (t₀ h u : ℝ)
    {z : ℂ} (hz : z.im ≤ 0) : DifferentiableAt ℂ (plattContourIntegrand k t₀ h u) z := by
  have hg : DifferentiableAt ℂ (fun z : ℂ =>
      Complex.Gamma ((1 / 4 : ℂ) + ((z + (t₀ : ℂ)) / 2) * Complex.I)) z := by
    apply (Complex.differentiableAt_Gamma _ ?_).comp z (by fun_prop)
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num [Complex.mul_re, Complex.div_ofNat_im] at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold plattContourIntegrand
  exact (hg.mul (by fun_prop)).mul (by fun_prop)

/-- Each connecting edge vanishes, in either horizontal direction. -/
theorem tendsto_integral_plattContour_right_edge_zero (m k : ℕ) (t₀ u : ℝ)
    {h ε : ℝ} (hh : 0 < h) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..(-plattRightShift m),
      plattContourIntegrand k t₀ h u (((ε * T : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  apply Complex.tendsto_integral_vertical_zero_of_bound
    (B := fun T => plattRightEdgeConstant m k t₀ h u *
      (T ^ k * Real.exp (-(1 / (4 * h ^ 2)) * T ^ 2)))
    (by simpa using (Real.tendsto_pow_mul_exp_neg_mul_sq k
      (by positivity : 0 < 1 / (4 * h ^ 2))).const_mul (plattRightEdgeConstant m k t₀ h u))
  filter_upwards [eventually_ge_atTop (max 1 (Real.pi * h ^ 2))] with T hT
  intro y hy
  have hT₁ : 1 ≤ T := (le_max_left _ _).trans hT
  have hT₂ : Real.pi * h ^ 2 ≤ T := (le_max_right _ _).trans hT
  have habs : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
  have ha : 0 ≤ plattRightShift m := by unfold plattRightShift; positivity
  have hy' : y ∈ Icc (-plattRightShift m) 0 := by
    simpa only [uIcc_of_ge (neg_nonpos.mpr ha)] using hy
  simpa only [habs] using norm_plattContourIntegrand_right_edge_le m k t₀ u hh
    (v := ε * T) (by simpa only [habs] using hT₁)
    (by simpa only [habs] using hT₂) hy'

/-- The real restriction is integrable, with the genuine Fourier phase. -/
theorem integrable_plattContourIntegrand_real (k : ℕ) (t₀ u : ℝ)
    {h : ℝ} (hh : 0 < h) : Integrable (fun v : ℝ => plattContourIntegrand k t₀ h u v) := by
  apply (integrable_plattWindowKernel k t₀ hh).norm.mono'
    (((measurable_plattContourIntegrand k t₀ h u).comp (by fun_prop)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro v
  change ‖plattContourIntegrand k t₀ h u (v : ℂ)‖ ≤ ‖plattWindowKernel k t₀ h v‖
  rw [plattContourIntegrand_real, norm_mul, Complex.norm_exp]
  simp

/-- The Fourier transform is exactly the integral of the real restriction. -/
theorem fourier_plattWindowKernel_eq_integral (k : ℕ) (t₀ h u : ℝ) :
    𝓕 (plattWindowKernel k t₀ h) u = ∫ v : ℝ, plattContourIntegrand k t₀ h u v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    dsimp only
    rw [plattContourIntegrand_real]
    rfl)

/-- The contour shift is an identity of actual integrals, not a new assumption. -/
theorem fourier_plattWindowKernel_eq_right_integral (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    𝓕 (plattWindowKernel k t₀ h) u = ∫ v : ℝ, plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_plattWindowKernel_eq_integral]
  apply Complex.integral_horizontal_eq_of_tendsto_edges
  · intro z hz
    have ha : 0 ≤ plattRightShift m := by unfold plattRightShift; positivity
    have hz' : z.im ∈ Icc (-plattRightShift m) 0 := by
      simpa only [uIcc_of_ge (neg_nonpos.mpr ha)] using hz
    exact differentiableAt_plattContourIntegrand_of_im_nonpos k t₀ h u hz'.2
  · exact integrable_plattContourIntegrand_real k t₀ u hh
  · exact integrable_plattContourIntegrand_right m k hm ht₀ hh u
  · simpa using tendsto_integral_plattContour_right_edge_zero m k t₀ u hh
      (ε := 1) (by norm_num)
  · simpa using tendsto_integral_plattContour_right_edge_zero m k t₀ u hh
      (ε := -1) (by norm_num)

/-- Rightward contour decay for the actual Fourier transform at every order. -/
theorem norm_fourier_plattWindowKernel_le_right_shift (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
        2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2)) * plattScalarCMajorant m k t₀ h := by
  rw [fourier_plattWindowKernel_eq_right_integral m k hm ht₀ hh u]
  exact norm_integral_plattContourIntegrand_right_le m k hm ht₀ hh u

end PrimeFactorUnimodality
