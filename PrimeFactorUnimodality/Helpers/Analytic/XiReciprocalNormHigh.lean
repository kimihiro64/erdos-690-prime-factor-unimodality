import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalCountIntegral
import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormWindow

/-! # An explicit reciprocal-norm bound above height ten

The proved counting envelope bounds both the endpoint and the entire Abel
integral. The lower endpoint count is nonnegative and may be dropped for
an upper bound. The resulting expression contains only real logarithms.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Set

/-- An elementary majorant for the positive-ordinate reciprocal norm on `(a,b]`. -/
def xiReciprocalNormWindowBound (a b : ℝ) : ℝ :=
  xiReciprocalCountEnvelope b / b +
    xiReciprocalCountPrimitive b - xiReciprocalCountPrimitive a

/-- All positive-ordinate zeros in the window are bounded without a low-gap input. -/
theorem sum_xi_reciprocal_norm_window_le_explicit {a b : ℝ}
    (ha : 10 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ xiHeightWindowIndices a b, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiReciprocalNormWindowBound a b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hker : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Icc a b) :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (ha0.trans_le ht.1).ne')).integrableOn_Icc
  have hcount : IntegrableOn (fun t => (xiZeroCount t : ℝ) / t ^ 2) (Icc a b) := by
    simpa only [mul_one_div] using integrableOn_xiZeroCount_mul hker
  have hI : (∫ t in Icc a b, (xiZeroCount t : ℝ) / t ^ 2) ≤
      ∫ t in Icc a b, xiReciprocalCountEnvelope t / t ^ 2 := by
    apply integral_mono_ae hcount
      (continuousOn_xiReciprocalCountEnvelope_div_sq ha0).integrableOn_Icc
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_le_div_of_nonneg_right
      (xiZeroCount_le_reciprocal_envelope (ha.trans ht.1)) (sq_nonneg t)
  have hB := div_le_div_of_nonneg_right
    (xiZeroCount_le_reciprocal_envelope (ha.trans hab)) hb0.le
  have hA : 0 ≤ (xiZeroCount a : ℝ) / a := by positivity
  rw [integral_xiReciprocalCountEnvelope_div_sq ha0 hab] at hI
  have hs := sum_xi_reciprocal_norm_window_le ha0 hab
  unfold xiReciprocalNormWindowBound
  linarith

end

end PrimeFactorUnimodality
