import PrimeFactorUnimodality.Helpers.Analytic.TuringLittlewood
import PrimeFactorUnimodality.Helpers.Analytic.TuringPhaseBounds

/-! # Explicit integrated discrepancy for the actual zero count

The complete argument bound and the exact phase normalization give a
numerical upper budget for the existing closed-count remainder. Its
interval-width coefficient is `15/16`, leaving room to detect an omitted
multiplicity label. No zero-location or numerical sign input is required.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Set

/-- A proved upper budget for the integrated, unshifted counting remainder above height 32. -/
def turingCountErrorBudget (a b : ℝ) : ℝ :=
  (15 / 16 : ℝ) * (b - a) + ((19 / 2 : ℝ) * Real.log (5 * b) + 95) / Real.pi

/-- Integrating the smooth phase retains its exact `7/8`-type offset below a unit count. -/
theorem integral_turingCountingPhase_sub_main_le {a b : ℝ} (ha : 32 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, turingCountingPhase t) -
        Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) ≤
      (15 / 16 : ℝ) * Real.pi * (b - a) := by
  have ha0 : 0 < a := by linarith
  have hi := (intervalIntegrable_turingCountingPhase ha0 hab).sub
    ((intervalIntegrable_xiZeroCountingMainTerm ha0 hab).const_mul Real.pi)
  have h := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (15 / 16 : ℝ) * Real.pi) volume a b)
    (fun t ht => turingCountingPhase_sub_main_le_fifteen_sixteenths (ha.trans ht.1))
  rw [intervalIntegral.integral_sub (intervalIntegrable_turingCountingPhase ha0 hab)
    ((intervalIntegrable_xiZeroCountingMainTerm ha0 hab).const_mul Real.pi),
    intervalIntegral.integral_const_mul, integral_xiZeroCountingMainTerm ha0 hab,
    intervalIntegral.integral_const] at h
  simpa only [smul_eq_mul, mul_comm (b - a)] using h

/-- The actual integrated counting remainder has an unconditional explicit upper bound. -/
theorem integral_xiZeroCountingRemainder_le_turingBudget {a b : ℝ}
    (ha : 32 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, xiZeroCountingRemainder t) ≤ turingCountErrorBudget a b := by
  have he := pi_mul_integral_xiZeroCountingRemainder
    (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < a) hab
  have harg := abs_integral_turingZetaArgument_le
    (by norm_num : (1 : ℝ) < 2) (by linarith : 1 ≤ a) hab
  have hp := integral_turingCountingPhase_sub_main_le ha hab
  apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
  have hbudget : Real.pi * turingCountErrorBudget a b =
      (15 / 16 : ℝ) * Real.pi * (b - a) + (19 / 2 : ℝ) * Real.log (5 * b) + 95 := by
    unfold turingCountErrorBudget
    field_simp
    ring
  rw [hbudget]
  linarith [le_abs_self (∫ t in a..b, turingZetaArgument 2 t)]

/-- The total multiplicity count is bounded by its exact smooth integral plus the explicit budget. -/
theorem integral_xiZeroCount_le_turingBudget {a b : ℝ} (ha : 32 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, (xiZeroCount t : ℝ)) ≤
      xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a + turingCountErrorBudget a b := by
  have h := integral_xiZeroCountingRemainder_le_turingBudget ha hab
  rw [integral_xiZeroCountingRemainder (by linarith) hab] at h
  linarith

end

end PrimeFactorUnimodality
