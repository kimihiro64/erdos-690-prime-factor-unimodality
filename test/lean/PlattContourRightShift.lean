import PrimeFactorUnimodality.Helpers.Analytic.PlattContourRightShift

/-! The genuine Fourier transform is identified with the shifted integral at arbitrary order. -/

open MeasureTheory PrimeFactorUnimodality
open scoped FourierTransform Topology

example (m k : ℕ) (t₀ u : ℝ) {h : ℝ} (hh : 0 < h) :
    Filter.Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..(-plattRightShift m),
      plattContourIntegrand k t₀ h u ((-T : ℝ) + (y : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  simpa using tendsto_integral_plattContour_right_edge_zero m k t₀ u hh
    (ε := -1) (by norm_num)

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    𝓕 (plattWindowKernel k t₀ h) u = ∫ v : ℝ, plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((-(2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I) :=
  fourier_plattWindowKernel_eq_right_integral m k hm ht₀ hh u

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
        2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2)) * plattScalarCMajorant m k t₀ h :=
  norm_fourier_plattWindowKernel_le_right_shift m k hm ht₀ hh u

example : ‖𝓕 (plattWindowKernel 0 1000 1) 1‖ ≤
    Real.exp (25 / 8 - 5 * Real.pi) * plattScalarCMajorant 1 0 1000 1 := by
  convert norm_fourier_plattWindowKernel_le_right_shift 1 0 (by omega)
    (t₀ := 1000) (h := 1) (by norm_num) (by norm_num) 1 using 1
  congr 2
  norm_num
  ring
