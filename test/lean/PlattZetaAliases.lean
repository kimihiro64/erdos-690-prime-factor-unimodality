import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaPoisson

/-! Actual zeta symmetry, both alias budgets, signed centers and the Poisson connection. -/

open PrimeFactorUnimodality
open scoped ComplexConjugate FourierTransform

example (t₀ h v : ℝ) : conj (plattZetaWindow 1 t₀ h v) = -plattZetaWindow 1 t₀ h v := by
  simpa using conj_plattZetaWindow 1 t₀ h v

example (k : ℕ) (t₀ h x : ℝ) :
    ‖𝓕 (plattZetaWindow k t₀ h) (-x)‖ = ‖𝓕 (plattZetaWindow k t₀ h) x‖ :=
  norm_fourier_plattZetaWindow_neg k t₀ h x

example (k : ℕ) (t₀ h x : ℝ) :
    ‖plattZetaContourResidueValue k t₀ h x‖ =
      ‖plattZetaContourResidueValue k t₀ h 0‖ * Real.exp (-Real.pi * x) :=
  norm_plattZetaContourResidueValue_eq_zero_mul_exp k t₀ h x

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    ‖𝓕 (plattZetaWindow k t₀ h) x‖ ≤
      ∑ i : Bool, plattZetaEnvelopeCoeff m k t₀ h i *
        Real.exp (-plattZetaEnvelopeRate m i * |x|) :=
  norm_fourier_plattZetaWindow_le_envelope m k hm ht₀ hh x

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h A x d : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (hx : |x| + d ≤ A) :
    ‖plattZetaFourierPeriodization k t₀ h A x - 𝓕 (plattZetaWindow k t₀ h) x‖ ≤
      plattZetaFourierAliasBound m k t₀ h A d :=
  norm_plattZetaFourierPeriodization_sub_le m k hm ht₀ hh hA hx

example (k : ℕ) {h B v : ℝ} (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    ‖plattZetaTimePeriodization k (-1000) h B v - plattZetaWindow k (-1000) h v‖ ≤
      plattZetaTimeAliasBound k (-1000) h B :=
  norm_plattZetaTimePeriodization_sub_le k (-1000) hh hB hk hv

example {h B : ℝ} (hh : 0 < h) (hk : 4 * h ^ 2 < B ^ 2) :
    0 < 1 - Real.exp (2 - B ^ 2 / (2 * h ^ 2)) := by
  simpa [plattZetaTimeDegree] using
    plattZetaTimeAlias_denominator_pos 0 hh (by simpa using hk) true

example (k : ℕ) {t₀ h B v : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    ‖((B⁻¹ : ℝ) : ℂ) * (∑' n : ℤ, 𝓕 (plattZetaWindow k t₀ h) ((n : ℝ) / B) *
        fourier n ((v / B : ℝ) : UnitAddCircle)) - plattZetaWindow k t₀ h v‖ ≤
      plattZetaTimeAliasBound k t₀ h B :=
  norm_plattZetaFourierSeries_sub_window_le k ht₀ hh hB hk hv
