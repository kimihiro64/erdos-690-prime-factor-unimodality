import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowFourier

/-! The bounds concern the full complex critical-line kernel, with the paper's scaling. -/

open MeasureTheory PrimeFactorUnimodality
open scoped FourierTransform

example (k : ℕ) (t₀ h v : ℝ) :
    plattWindowKernel k t₀ h v =
      Complex.Gamma (((1 / 2 : ℂ) + Complex.I * ((v + t₀ : ℝ) : ℂ)) / 2) *
        (Real.exp (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) : ℂ) *
          (-2 * (Real.pi : ℂ) * Complex.I * (v : ℂ)) ^ k := by
  have hg : (1 / 4 : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I =
      ((1 / 2 : ℂ) + Complex.I * ((v + t₀ : ℝ) : ℂ)) / 2 := by push_cast; ring
  have hf : (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) =
      -2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) := by push_cast; ring
  simp only [plattWindowKernel, hg, hf]

example (t₀ h v : ℝ) :
    ‖plattWindowKernel 0 t₀ h v‖ ≤
      plattQuarterGammaConstant * Real.exp (-v ^ 2 / (2 * h ^ 2)) := by
  simpa only [pow_zero, mul_one] using norm_plattWindowKernel_le 0 t₀ h v

example (k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (plattWindowKernel k t₀ h) := integrable_plattWindowKernel k t₀ hh

example (k : ℕ) (t₀ h v : ℝ) :
    ‖plattWindowKernel k t₀ h v‖ ≤
      5 * (2 * Real.pi * |v|) ^ k * Real.exp (-v ^ 2 / (2 * h ^ 2)) :=
  norm_plattWindowKernel_le_five k t₀ h v

example (k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ v : ℝ, ‖plattWindowKernel k t₀ h v‖) ≤ plattWindowL1Bound k h :=
  integral_norm_plattWindowKernel_le k t₀ hh

example (k : ℕ) (t₀ ξ : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖𝓕 (plattWindowKernel k t₀ h) ξ‖ ≤ plattWindowL1Bound k h :=
  norm_fourier_plattWindowKernel_le k t₀ ξ hh
