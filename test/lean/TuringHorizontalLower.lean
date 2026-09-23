import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalLower

/-! # Exact interfaces and boundary cases for the actual logarithmic-ratio chain -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set

example {T : ℝ} (hT : T ≠ 0) :
    IntervalIntegrable (turingZetaLogDecrement T) volume 0 1 := by
  exact PrimeFactorUnimodality.intervalIntegrable_turingZetaLogDecrement hT

example (T : ℝ) :
    (∫ x in (0 : ℝ)..1, turingZetaLogDecrement T x) = turingShiftedLogIntegral 1 T := by
  exact PrimeFactorUnimodality.integral_turingZetaLogDecrement T

example {T : ℝ} (hT : T ≠ 0) :
    -(8 * Real.log (|T| / 2 + 3) + 90) ≤ turingShiftedLogIntegral 1 T := by
  exact PrimeFactorUnimodality.turingShiftedLogIntegral_one_ge hT

example {T : ℝ} (hT : T ≠ 0) :
    -(8 * Real.log (|T| / 2 + 3) + 94) ≤ turingHorizontalIntegral T := by
  exact PrimeFactorUnimodality.turingHorizontalIntegral_ge hT

example : -(8 * Real.log (7 / 2) + 94) ≤ turingHorizontalIntegral 1 := by
  convert turingHorizontalIntegral_ge (T := 1) (by norm_num) using 1
  norm_num

example : -(8 * Real.log (7 / 2) + 94) ≤ turingHorizontalIntegral (-1) := by
  convert turingHorizontalIntegral_ge (T := -1) (by norm_num) using 1
  norm_num

example {T : ℝ} (hT : T ≠ 0) :
    -(8 * Real.log (|T| / 2 + 3) + 94) ≤ turingHorizontalIntegral (-T) := by
  simpa using turingHorizontalIntegral_ge (neg_ne_zero.mpr hT)

end

end PrimeFactorUnimodality.Tests
