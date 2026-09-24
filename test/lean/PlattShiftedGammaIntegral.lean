import PrimeFactorUnimodality.Helpers.Analytic.PlattShiftedGammaIntegral

/-! Both displaced integrals retain the exact Gaussian and Fourier factors. -/

open MeasureTheory PrimeFactorUnimodality

example (k : ℕ) (t₀ h u v : ℝ) :
    plattContourIntegrand k t₀ h u (v : ℂ) =
      Complex.exp (((-2 * Real.pi * v * u : ℝ) : ℂ) * Complex.I) *
        plattWindowKernel k t₀ h v := plattContourIntegrand_real k t₀ h u v

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    Integrable (fun v : ℝ => plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((-(2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I)) :=
  integrable_plattContourIntegrand_right m k hm ht₀ hh u

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    Integrable (fun v : ℝ => plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) * Complex.I)) :=
  integrable_plattContourIntegrand_left m k hm ht₀ hh u

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖∫ v : ℝ, plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((-(2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
        2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2)) * plattScalarCMajorant m k t₀ h :=
  norm_integral_plattContourIntegrand_right_le m k hm ht₀ hh u

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖∫ v : ℝ, plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
        2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2)) *
          (plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h) :=
  norm_integral_plattContourIntegrand_left_le m k hm ht₀ hh u
