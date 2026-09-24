import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds

/-! # Transporting the reciprocal-mass budget to smaller heights

The endpoint term and the counting-envelope primitive simplify to an
increasing squared logarithm minus a reciprocal. Thus decreasing the verified
height never enlarges the explicit low-zero mass bound. The existing scalar
bound at a billion supplies the same allowance at every smaller height.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The endpoint and primitive cancel the linear logarithm and boundary correction. -/
theorem xiReciprocalNormWindowBound_eq_logSquare (a : ℝ) {T : ℝ} (hT : 0 < T) :
    xiReciprocalNormWindowBound a T =
      Real.log (T / (2 * π)) ^ 2 / (4 * π) - (Real.log (2 * π) + 1) / (2 * π) -
        1 / T - xiReciprocalCountPrimitive a := by
  unfold xiReciprocalNormWindowBound xiReciprocalCountEnvelope xiZeroCountingMainTerm
  rw [xiReciprocalCountPrimitive, Real.log_div hT.ne' (by positivity : 2 * π ≠ 0)]
  field_simp
  ring

/-- Enlarging the upper height increases the explicit reciprocal window budget. -/
theorem xiReciprocalNormWindowBound_mono_height (a : ℝ) {T U : ℝ}
    (hT : 10 ≤ T) (hTU : T ≤ U) :
    xiReciprocalNormWindowBound a T ≤ xiReciprocalNormWindowBound a U := by
  have hTpos : 0 < T := by linarith
  have hUpos : 0 < U := hTpos.trans_le hTU
  have hp : 0 < 2 * π := by positivity
  have hbase : 1 ≤ T / (2 * π) := (le_div_iff₀ hp).mpr (by linarith [pi_lt_four])
  have hlog := Real.log_le_log (div_pos hTpos hp) (div_le_div_of_nonneg_right hTU hp.le)
  have hsquare := pow_le_pow_left₀ (Real.log_nonneg hbase) hlog 2
  have hquot := div_le_div_of_nonneg_right hsquare (by positivity : 0 ≤ 4 * π)
  have hinv := one_div_le_one_div_of_le hTpos hTU
  rw [xiReciprocalNormWindowBound_eq_logSquare a hTpos,
    xiReciprocalNormWindowBound_eq_logSquare a hUpos]
  linarith

/-- The prefix minimum is independent of the upper height. -/
theorem xiLowReciprocalNormBound_mono_height (a δ : ℝ) {T U : ℝ}
    (hT : 10 ≤ T) (hTU : T ≤ U) :
    xiLowReciprocalNormBound a T δ ≤ xiLowReciprocalNormBound a U δ := by
  unfold xiLowReciprocalNormBound
  linarith [xiReciprocalNormWindowBound_mono_height a hT hTU]

/-- Every smaller admissible height inherits the proved seventy-unit mass budget. -/
theorem xiLowReciprocalNormBound_half_le_of_le_billion {T : ℝ}
    (hT : 10 ≤ T) (hTU : T ≤ 1000000000) :
    xiLowReciprocalNormBound 10 T (1 / 2) ≤ (70 : ℝ) :=
  (xiLowReciprocalNormBound_mono_height 10 (1 / 2) hT hTU).trans
    xiLowReciprocalNormBound_billion_half_le

end

end PrimeFactorUnimodality
