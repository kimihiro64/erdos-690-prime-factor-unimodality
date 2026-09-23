import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringLittlewood

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ T in a..b, turingZetaArgument σ T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a := by
  exact PrimeFactorUnimodality.integral_turingZetaArgument_eq_horizontal_sub hσ ha hab

example {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Real.pi * (∫ T in a..b, xiZeroCountingRemainder T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a +
        (∫ T in a..b, turingCountingPhase T) -
          Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) := by
  exact PrimeFactorUnimodality.pi_mul_integral_xiZeroCountingRemainder_eq_horizontal ha hab

example {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |∫ T in a..b, turingZetaArgument σ T| ≤ (19 / 2 : ℝ) * Real.log (5 * b) + 95 := by
  exact PrimeFactorUnimodality.abs_integral_turingZetaArgument_le hσ ha hab

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ T in b..a, turingZetaArgument 2 T) =
      turingHorizontalIntegral a - turingHorizontalIntegral b := by
  rw [intervalIntegral.integral_symm,
    integral_turingZetaArgument_eq_horizontal_sub (by norm_num) ha hab]
  ring

example {a : ℝ} (ha : 0 < a) : (∫ T in a..a, turingZetaArgument 2 T) =
    turingHorizontalIntegral a - turingHorizontalIntegral a :=
  integral_turingZetaArgument_eq_horizontal_sub (by norm_num) ha le_rfl

example {b : ℝ} (hb : 1 ≤ b) : |∫ T in (1 : ℝ)..b, turingZetaArgument 2 T| ≤
    (19 / 2 : ℝ) * Real.log (5 * b) + 95 :=
  abs_integral_turingZetaArgument_le (by norm_num) le_rfl hb

end

end PrimeFactorUnimodality.Tests
