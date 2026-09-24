import PrimeFactorUnimodality.Helpers.Analytic.PlattContourResidueNorm

/-! The negative-frequency contour retains every pole and the first-shift correction. -/

open MeasureTheory PrimeFactorUnimodality
open scoped FourierTransform

example (m n : ℕ) {t₀ T : ℝ} (hT : |t₀| < T) :
    plattGammaPole n t₀ ∈ Complex.Rectangle ((-T : ℝ) : ℂ) (plattLeftContourCorner m T) ↔
      n ≤ m :=
  plattGammaPole_mem_rectangle_iff m n hT

example (m k : ℕ) {t₀ T : ℝ} (hT : |t₀| < T) (h u : ℝ) :
    RectangleIntegral' (plattContourIntegrand k t₀ h u)
      ((-T : ℝ) : ℂ) (plattLeftContourCorner m T) =
      ∑ n ∈ Finset.range (m + 1), plattContourResidueValue n k t₀ h u :=
  rectangleIntegral_plattContourIntegrand_eq_sum m k hT h u

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    𝓕 (plattWindowKernel k t₀ h) u =
      (∫ v : ℝ, plattContourIntegrand k t₀ h u
        ((v : ℂ) + (((2 * (m : ℝ) + 3 / 2 : ℝ)) : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ n ∈ Finset.range (m + 1), plattContourResidueValue n k t₀ h u :=
  fourier_plattWindowKernel_eq_left_integral_add_residues m k hm ht₀ hh u

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
        2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2)) *
        (plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h) +
      2 * Real.pi * ∑ n ∈ Finset.range (m + 1), plattContourResidueNorm n k t₀ h u :=
  norm_fourier_plattWindowKernel_le_left_explicit m k hm ht₀ hh u

example : ‖plattContourResidueValue 0 0 0 1 (-1)‖ =
    2 * Real.exp (1 / 8 - Real.pi) := by
  rw [norm_plattContourResidueValue]
  norm_num [plattContourResidueNorm]
  congr 2
  ring
