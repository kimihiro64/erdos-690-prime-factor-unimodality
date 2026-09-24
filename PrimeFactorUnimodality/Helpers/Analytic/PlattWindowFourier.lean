import Mathlib.Analysis.Fourier.FourierTransform
import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowKernel

set_option autoImplicit false

/-! # Fourier integral of the windowed Gamma kernel

The actual critical-line kernel supplies an absolutely convergent Fourier
integral at every real frequency. Its integral-norm estimate bounds the
transform uniformly. This does not assert the stronger shifted-contour
decay or a finite Fourier approximation.
-/

open MeasureTheory
open scoped FourierTransform Real

namespace PrimeFactorUnimodality

/-- The Fourier phase preserves the integrability already proved for the kernel. -/
theorem integrable_fourier_plattWindowKernel (k : ℕ) (t₀ ξ : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (fun v : ℝ => Real.fourierChar (-(v * ξ)) • plattWindowKernel k t₀ h v) := by
  simpa [mul_comm] using
    (Real.fourierIntegral_convergent_iff (f := plattWindowKernel k t₀ h) ξ).mpr
      (integrable_plattWindowKernel k t₀ hh)

/-- The genuine Fourier transform is uniformly bounded by the explicit Gaussian moment. -/
theorem norm_fourier_plattWindowKernel_le (k : ℕ) (t₀ ξ : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖𝓕 (plattWindowKernel k t₀ h) ξ‖ ≤ plattWindowL1Bound k h := by
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
    volume (innerₗ ℝ) (plattWindowKernel k t₀ h) ξ).trans
      (integral_norm_plattWindowKernel_le k t₀ hh)

end PrimeFactorUnimodality
