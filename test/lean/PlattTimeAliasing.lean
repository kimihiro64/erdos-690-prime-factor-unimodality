import PrimeFactorUnimodality.Helpers.Analytic.PlattShiftedFourierAliasing
import PrimeFactorUnimodality.Helpers.Analytic.PlattTimeAliasing

/-! Actual time aliases, the central-cell boundary, and the complete Poisson series. -/

open PrimeFactorUnimodality
open scoped FourierTransform

example (k : ℕ) (t₀ : ℝ) {h B v : ℝ} (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    ‖plattTimePeriodization k t₀ h B v - plattWindowKernel k t₀ h v‖ ≤
      plattTimeAliasBound k h B :=
  norm_plattTimePeriodization_sub_le k t₀ hh hB hk hv

example : ‖plattTimePeriodization 1 (-1000) 1 4 2 - plattWindowKernel 1 (-1000) 1 2‖ ≤
    40 * Real.pi * Real.exp (-2) / (1 - Real.exp (-6)) := by
  have ht := norm_plattTimePeriodization_sub_le 1 (-1000) (h := 1) (B := 4) (v := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert ht using 1
  norm_num [plattTimeAliasBound]
  ring

example (k : ℕ) {t₀ h B v : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    ‖((B⁻¹ : ℝ) : ℂ) * (∑' n : ℤ, 𝓕 (plattWindowKernel k t₀ h) ((n : ℝ) / B) *
        fourier n ((v / B : ℝ) : UnitAddCircle)) - plattWindowKernel k t₀ h v‖ ≤
      plattTimeAliasBound k h B :=
  norm_plattFourierSeries_sub_kernel_le k ht₀ hh hB hk hv

example {h B : ℝ} (hh : 0 < h) (hB : 0 < B) :
    0 < 1 - Real.exp (-B ^ 2 / (2 * h ^ 2)) := by
  simpa [neg_div] using
    plattTimeAlias_denominator_pos 0 hh (B := B) (by simpa using sq_pos_of_pos hB)

example : ‖plattFourierPeriodization 0 1000 1 4 (-3) -
      𝓕 (plattWindowKernel 0 1000 1) (-3)‖ ≤
    plattFourierAliasBoundWithMargin 1 0 1000 1 4 1 := by
  convert norm_plattFourierPeriodization_shift_sub_le 1 0 (by omega)
    (t₀ := 1000) (h := 1) (A := 4) (u := -2) (s := 1) (D := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
