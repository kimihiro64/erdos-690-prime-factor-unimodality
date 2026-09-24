import PrimeFactorUnimodality.Helpers.Analytic.PlattNegativeGammaIntegral

/-! The negative-line integral retains the correction at the first admissible shift. -/

open MeasureTheory PrimeFactorUnimodality

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    Integrable (plattNegativeGammaWindow m k t₀ h) :=
  integrable_plattNegativeGammaWindow m k hm ht₀ hh

example (k : ℕ) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    plattNegativeScalarC 1 k t₀ h ≤ (8 / 3) * plattScalarCMajorant 1 k t₀ h := by
  simpa only [plattNegativeGammaFactor, show (1 : ℕ) < 2 by omega, ite_true] using
    plattNegativeScalarC_le_majorant 1 k (by omega) ht₀ hh

example (m k : ℕ) (hm : 2 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    plattNegativeScalarC m k t₀ h ≤ plattScalarCMajorant m k t₀ h := by
  simpa only [plattNegativeGammaFactor, ite_eq_right (show ¬ m < 2 by omega), one_mul] using
    plattNegativeScalarC_le_majorant m k (by omega) ht₀ hh
