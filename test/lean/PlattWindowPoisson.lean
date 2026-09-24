import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowPoisson

/-! The actual periodization, all residue coefficients and the reciprocal-period scaling. -/

open PrimeFactorUnimodality
open scoped FourierTransform

example : plattFourierEnvelopeRate 1 none = 5 * Real.pi := by
  norm_num [plattFourierEnvelopeRate]
  ring

example : plattFourierEnvelopeCoeff 1 0 0 1 none =
    (8 / 3) * plattScalarCMajorant 1 0 0 1 * Real.exp (49 / 8) := by
  norm_num [plattFourierEnvelopeCoeff, plattNegativeGammaFactor]

example : plattFourierEnvelopeCoeff 1 0 0 1 (some ⟨0, by omega⟩) =
    4 * Real.pi * Real.exp (1 / 8) := by
  norm_num [plattFourierEnvelopeCoeff, plattContourResidueNorm]
  ring

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h A u : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (hu : |u| ≤ A / 2) :
    ‖plattFourierPeriodization k t₀ h A u - 𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      plattFourierAliasBound m k t₀ h A :=
  norm_plattFourierPeriodization_sub_le m k hm ht₀ hh hA hu

example (k : ℕ) {t₀ h B : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (v : ℝ) :
    (∑' n : ℤ, plattWindowKernel k t₀ h (v + (n : ℝ) * B)) =
      ((B⁻¹ : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 (plattWindowKernel k t₀ h) ((n : ℝ) / B) *
        fourier n ((v / B : ℝ) : UnitAddCircle) :=
  tsum_plattWindowKernel_eq_fourier_series k ht₀ hh hB v
