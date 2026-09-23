import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringZetaLogStep

/-! # Exact interfaces and boundary cases for the actual logarithmic-ratio chain -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set

example (T : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.log ‖(x : ℂ) + ((1 / 2 : ℂ) + T * I)‖ -
      Real.log ‖(x : ℂ) + ((1 / 2 : ℂ) + T * I) - 1‖ := by
  exact PrimeFactorUnimodality.turing_pole_log_gain_nonneg T hx

example {T x : ℝ} (hT : T ≠ 0) (hx : 0 ≤ x)
    (hxi : riemannXi ((x : ℂ) + ((1 / 2 : ℂ) + T * I)) ≠ 0) :
    -turingXiLogIncrement T x - 2 ≤ turingZetaLogDecrement T x := by
  exact PrimeFactorUnimodality.turingZetaLogDecrement_ge hT hx hxi

example (T : ℝ) : 0 ≤ Real.log ‖((1 / 2 : ℂ) + T * I)‖ -
    Real.log ‖((1 / 2 : ℂ) + T * I) - 1‖ := by
  simpa using turing_pole_log_gain_nonneg T (x := 0) le_rfl

example (x : ℝ) (hx : 0 ≤ x)
    (hxi : riemannXi ((x : ℂ) + ((1 / 2 : ℂ) + (-1 : ℝ) * I)) ≠ 0) :
    -turingXiLogIncrement (-1) x - 2 ≤ turingZetaLogDecrement (-1) x :=
  turingZetaLogDecrement_ge (by norm_num) hx hxi

end

end PrimeFactorUnimodality.Tests
