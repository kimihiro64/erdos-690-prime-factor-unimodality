import PrimeFactorUnimodality.Helpers.Analytic.XiHeightBand
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInitial

/-! # The proved initial zero-free region on a bounded height band

Monotonicity of the logarithm converts the actual pointwise region with
constant `56` into a uniform gap on a finite band above `10^9`. The result
uses no low-height location hypothesis and makes no RH assumption.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The initial gap at an upper cutoff is positive throughout the high range. -/
theorem xi_initial_gap_pos {T : ℝ} (hT : 10 ^ 9 ≤ T) :
    0 < 1 / (56 * Real.log T) := by
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  positivity

/-- Every band zero satisfies the uniform gap supplied by the existing initial region. -/
theorem xi_height_band_re_le_initial_gap {H T : ℝ} (hH : 10 ^ 9 ≤ H)
    {p : RiemannXiDivisorZeroIndex} (hp : p ∈ xiHeightBandIndices H T) :
    (riemannXiDivisorZeroValue p).re ≤ 1 - 1 / (56 * Real.log T) := by
  obtain ⟨hlo, hhi⟩ := (mem_xiHeightBandIndices H T p).mp hp
  have ht := hH.trans hlo
  have hl : 0 < Real.log |(riemannXiDivisorZeroValue p).im| :=
    Real.log_pos (by linarith)
  have hg := xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero p) ht
  have hlog := Real.log_le_log (by linarith : 0 < |(riemannXiDivisorZeroValue p).im|) hhi.le
  have hinv := one_div_le_one_div_of_le (by positivity :
    0 < 56 * Real.log |(riemannXiDivisorZeroValue p).im|)
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 56))
  linarith

end

end PrimeFactorUnimodality
