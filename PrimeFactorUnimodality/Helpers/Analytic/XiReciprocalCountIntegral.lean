import PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingHigh

/-! # Integrating the proved xi counting envelope against the reciprocal square

The unconditional counting estimate is valid from height ten. Its envelope
has an elementary antiderivative after division by `t^2`; evaluating it
retains the logarithmic-square scale needed for reciprocal-norm mass.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The actual counting estimate's explicit upper envelope. -/
def xiReciprocalCountEnvelope (t : ℝ) : ℝ := xiZeroCountingMainTerm t + Real.log t + 17

/-- No supplied RvM estimate is needed for this bound. -/
theorem xiZeroCount_le_reciprocal_envelope {t : ℝ} (ht : 10 ≤ t) :
    (xiZeroCount t : ℝ) ≤ xiReciprocalCountEnvelope t := by
  have he := (abs_le.mp (abs_xiZeroCountingRemainder_le_log_add ht)).2
  unfold xiZeroCountingRemainder at he
  unfold xiReciprocalCountEnvelope
  linarith

/-- A primitive of the envelope divided by the height squared. -/
def xiReciprocalCountPrimitive (t : ℝ) : ℝ :=
  Real.log (t / (2 * π)) ^ 2 / (4 * π) - Real.log t / (2 * π) - (Real.log t + 18) / t

theorem hasDerivAt_xiReciprocalCountPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt xiReciprocalCountPrimitive (xiReciprocalCountEnvelope t / t ^ 2) t := by
  have hL : HasDerivAt (fun t : ℝ => Real.log (t / (2 * π))) t⁻¹ t := by
    apply (((hasDerivAt_id t).div_const (2 * π)).log
      (div_ne_zero ht.ne' (by positivity))).congr_deriv
    dsimp
    field_simp
  have hd := (((hL.pow 2).div_const (4 * π)).sub
    ((Real.hasDerivAt_log ht.ne').div_const (2 * π))).sub
      (((Real.hasDerivAt_log ht.ne').add_const 18).div (hasDerivAt_id t) ht.ne')
  apply hd.congr_deriv
  dsimp [xiReciprocalCountEnvelope, xiZeroCountingMainTerm]
  field_simp
  ring

theorem continuousOn_xiReciprocalCountEnvelope_div_sq {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => xiReciprocalCountEnvelope t / t ^ 2) (Icc a b) := by
  have hc : ContinuousOn xiReciprocalCountEnvelope (Icc a b) := by
    intro t ht
    exact (((hasDerivAt_xiZeroCountingMainTerm (ha.trans_le ht.1)).continuousAt.add
      (Real.continuousAt_log (ha.trans_le ht.1).ne')).add_const 17).continuousWithinAt
  exact hc.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')

/-- The whole finite-interval integral is an explicit endpoint difference. -/
theorem integral_xiReciprocalCountEnvelope_div_sq {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Icc a b, xiReciprocalCountEnvelope t / t ^ 2) =
      xiReciprocalCountPrimitive b - xiReciprocalCountPrimitive a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_xiReciprocalCountPrimitive (ha.trans_le ht.1)
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (continuousOn_xiReciprocalCountEnvelope_div_sq ha).integrableOn_Icc

end

end PrimeFactorUnimodality
