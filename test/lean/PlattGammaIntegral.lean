import PrimeFactorUnimodality.Helpers.Analytic.PlattGammaIntegral

/-! The actual scalar integral is integrable and controlled at every admissible order. -/

open MeasureTheory PrimeFactorUnimodality

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    Integrable (plattGammaWindow m k t₀ h) :=
  integrable_plattGammaWindow m k hm ht₀ hh

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    plattScalarC m k t₀ h ≤ plattScalarCMajorant m k t₀ h :=
  plattScalarC_le_majorant m k hm ht₀ hh

example : plattScalarC 1 0 1000 1 ≤ 1001 * Real.pi + Real.sqrt (2 * Real.pi) := by
  have h := plattScalarC_le_majorant 1 0 (by omega)
    (t₀ := 1000) (h := 1) (by norm_num) (by norm_num)
  have he : plattScalarCMajorant 1 0 1000 1 =
      1001 * Real.pi + Real.sqrt (2 * Real.pi) := by
    norm_num [plattScalarCMajorant, Finset.sum_range_succ, Real.Gamma_one_half_eq,
      ← Real.sqrt_eq_rpow]
    calc
      _ = 1001 / 2 * ((Real.sqrt 2) ^ 2 * (Real.sqrt Real.pi) ^ 2) +
          Real.sqrt 2 * Real.sqrt Real.pi := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt Real.pi_pos.le]
        ring
  exact h.trans_eq he
