import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogShift

/-! # Exact interfaces and boundary cases for LogShiftIntegral -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open MeasureTheory

example (u a b : ℝ) : IntervalIntegrable (fun x => Real.log |x - u|) volume a b :=
  Real.intervalIntegrable_log_abs_sub u a b

example (u : ℝ) : (∫ x in (0 : ℝ)..1, Real.log |x - u|) =
    (1 - u) * Real.log (1 - u) + u * Real.log u - 1 := Real.integral_log_abs_sub u

example {u : ℝ} (hu : |u| ≤ 1) : -2 ≤ ∫ x in (0 : ℝ)..1, Real.log |x - u| :=
  Real.neg_two_le_integral_log_abs_sub hu

example : (∫ x in (0 : ℝ)..1, Real.log |x|) = -1 := by
  simpa using Real.integral_log_abs_sub 0

example : (∫ x in (0 : ℝ)..1, Real.log |x - 1|) = -1 := by
  simpa using Real.integral_log_abs_sub 1

example : -2 ≤ ∫ x in (0 : ℝ)..1, Real.log |x - (-1)| :=
  Real.neg_two_le_integral_log_abs_sub (by norm_num)

end

end PrimeFactorUnimodality.Tests
