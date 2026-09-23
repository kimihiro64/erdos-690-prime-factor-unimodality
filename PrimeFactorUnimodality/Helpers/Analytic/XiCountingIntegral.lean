import PrimeFactorUnimodality.Helpers.Analytic.XiMissingCount

/-! # Exact integral of the smooth positive-zero counting model

The model already used by the Lehman formula has no constant offset.
Its explicit primitive removes numerical quadrature of the smooth term
from count-completeness budgets. The remaining integral is the actual
closed-count discrepancy, not an asserted bound for the zeta argument.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- A primitive of the existing zero-counting main term, with no constant offset. -/
def xiZeroCountingMainIntegral (T : ℝ) : ℝ :=
  T ^ 2 / (4 * π) * Real.log (T / (2 * π)) - 3 / (8 * π) * T ^ 2

/-- The explicit primitive differentiates to precisely the existing counting model. -/
theorem hasDerivAt_xiZeroCountingMainIntegral {T : ℝ} (hT : 0 < T) :
    HasDerivAt xiZeroCountingMainIntegral (xiZeroCountingMainTerm T) T := by
  have hq : T / (2 * π) ≠ 0 := ne_of_gt (by positivity : 0 < T / (2 * π))
  have h := ((((hasDerivAt_id T).pow 2).div_const (4 * π)).mul
    (((hasDerivAt_id T).div_const (2 * π)).log hq)).sub
    (((hasDerivAt_id T).pow 2).const_mul (3 / (8 * π)))
  convert h using 1
  · funext t
    rfl
  · dsimp [xiZeroCountingMainTerm]
    field_simp [ne_of_gt hT, ne_of_gt pi_pos]
    ring

/-- The smooth model is integrable on every positive ordered interval. -/
theorem intervalIntegrable_xiZeroCountingMainTerm {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable xiZeroCountingMainTerm volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  exact (hasDerivAt_xiZeroCountingMainTerm (ha.trans_le ht.1)).continuousAt.continuousWithinAt

/-- Evaluate the smooth counting integral using only its two endpoints. -/
theorem integral_xiZeroCountingMainTerm {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, xiZeroCountingMainTerm t) =
      xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_xiZeroCountingMainIntegral (ha.trans_le ht.1)
  · exact intervalIntegrable_xiZeroCountingMainTerm ha hab

/-- No count endpoint is dropped when separating its integrated discrepancy. -/
theorem integral_xiZeroCountingRemainder {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, xiZeroCountingRemainder t) =
      (∫ t in a..b, (xiZeroCount t : ℝ)) -
        (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) := by
  simp only [xiZeroCountingRemainder]
  rw [intervalIntegral.integral_sub (intervalIntegrable_xiZeroCount a b)
    (intervalIntegrable_xiZeroCountingMainTerm ha hab), integral_xiZeroCountingMainTerm ha hab]

end

end PrimeFactorUnimodality
