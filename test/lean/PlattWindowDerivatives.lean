import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowDerivatives

/-! Every weighted transform is the corresponding true derivative, including signed centers. -/

open PrimeFactorUnimodality
open scoped ContDiff FourierTransform

example (n k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    iteratedDeriv n (𝓕 (plattWindowKernel k t₀ h)) =
      𝓕 (plattWindowKernel (k + n) t₀ h) :=
  iteratedDeriv_fourier_plattWindowKernel n k t₀ hh

example (n : ℕ) {h : ℝ} (hh : 0 < h) :
    iteratedDeriv n (𝓕 (plattWindowKernel 0 (-1000) h)) =
      𝓕 (plattWindowKernel n (-1000) h) :=
  iteratedDeriv_fourier_plattWindowKernel_zero n (-1000) hh

example (n : ℕ) (t₀ u : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖iteratedDeriv n (𝓕 (plattWindowKernel 0 t₀ h)) u‖ ≤ plattWindowL1Bound n h := by
  simpa only [Nat.zero_add] using norm_iteratedDeriv_fourier_plattWindowKernel_le n 0 t₀ u hh

example (k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (𝓕 (plattWindowKernel k t₀ h)) :=
  contDiff_fourier_plattWindowKernel k t₀ hh
