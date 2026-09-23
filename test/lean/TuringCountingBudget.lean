import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringCountingBudget

/-! # Exact interfaces and endpoint cases for the proved Turing counting budget -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Set
open MeasureTheory

example {a b : ℝ} (ha : 32 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, turingCountingPhase t) -
        Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) ≤
      (15 / 16 : ℝ) * Real.pi * (b - a) := by
  exact PrimeFactorUnimodality.integral_turingCountingPhase_sub_main_le ha hab

example {a b : ℝ}
    (ha : 32 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, xiZeroCountingRemainder t) ≤ turingCountErrorBudget a b := by
  exact PrimeFactorUnimodality.integral_xiZeroCountingRemainder_le_turingBudget ha hab

example {a b : ℝ} (ha : 32 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, (xiZeroCount t : ℝ)) ≤
      xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a + turingCountErrorBudget a b := by
  exact PrimeFactorUnimodality.integral_xiZeroCount_le_turingBudget ha hab

example : turingCountErrorBudget 32 32 =
    ((19 / 2 : ℝ) * Real.log 160 + 95) / Real.pi := by
  norm_num [turingCountErrorBudget]

example {a : ℝ} (ha : 32 ≤ a) :
    (∫ t in a..a, xiZeroCountingRemainder t) ≤ turingCountErrorBudget a a :=
  integral_xiZeroCountingRemainder_le_turingBudget ha le_rfl

example : (∫ t in (32 : ℝ)..33, xiZeroCountingRemainder t) ≤
    (15 / 16 : ℝ) + ((19 / 2 : ℝ) * Real.log 165 + 95) / Real.pi := by
  have h := integral_xiZeroCountingRemainder_le_turingBudget
    (a := 32) (b := 33) le_rfl (by norm_num)
  norm_num [turingCountErrorBudget] at h
  exact h

end

end PrimeFactorUnimodality.Tests
