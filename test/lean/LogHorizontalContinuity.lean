import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.HorizontalContinuity

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example (w : ℂ) (t a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖(x : ℂ) + t * I - w‖) volume a b := by
  exact Complex.intervalIntegrable_log_norm_horizontal_sub w t a b

example (w : ℂ) (a b : ℝ) :
    Continuous (fun t : ℝ => ∫ x in a..b, Real.log ‖(x : ℂ) + t * I - w‖) := by
  exact Complex.continuous_integral_log_norm_horizontal_sub w a b

example : ContinuousAt (fun t : ℝ => ∫ x in (-1 : ℝ)..1,
    Real.log ‖(x : ℂ) + t * I‖) 0 := by
  simpa using (continuous_integral_log_norm_horizontal_sub 0 (-1) 1).continuousAt (x := 0)

example : ContinuousAt (fun t : ℝ => ∫ x in (0 : ℝ)..1,
    Real.log ‖(x : ℂ) + t * I‖) 0 := by
  simpa using (continuous_integral_log_norm_horizontal_sub 0 0 1).continuousAt (x := 0)

example (w : ℂ) (a b : ℝ) : ContinuousAt
    (fun t : ℝ => ∫ x in b..a, Real.log ‖(x : ℂ) + t * I - w‖) w.im :=
  (continuous_integral_log_norm_horizontal_sub w b a).continuousAt

end

end PrimeFactorUnimodality.Tests
