import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringLittlewoodReduction

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 0 < a) (hab : a ≤ b)
    (hc : ContinuousOn turingHorizontalIntegral (Icc a b)) :
    (∫ T in a..b, turingZetaArgument σ T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a := by
  exact PrimeFactorUnimodality.integral_turingZetaArgument_eq_horizontal_sub_of_continuous hσ ha hab hc

example {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 0 < a) (hab : a ≤ b)
    (hreg : ∀ T ∈ Icc a b, ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    (∫ T in a..b, turingZetaArgument σ T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a := by
  exact PrimeFactorUnimodality.integral_turingZetaArgument_eq_horizontal_sub_of_regular hσ ha hab hreg

example {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : ContinuousOn turingHorizontalIntegral (Icc a b)) :
    Real.pi * (∫ T in a..b, xiZeroCountingRemainder T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a +
        (∫ T in a..b, turingCountingPhase T) -
          Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) := by
  exact PrimeFactorUnimodality.pi_mul_integral_xiZeroCountingRemainder_eq_horizontal_of_continuous ha hab hc

example {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hc : ContinuousOn turingHorizontalIntegral (Icc a b)) :
    |∫ T in a..b, turingZetaArgument σ T| ≤ (19 / 2 : ℝ) * Real.log (5 * b) + 95 := by
  exact PrimeFactorUnimodality.abs_integral_turingZetaArgument_le_of_continuous hσ ha hab hc

example {a : ℝ} (ha : 0 < a) : (∫ T in a..a, turingZetaArgument 2 T) =
    turingHorizontalIntegral a - turingHorizontalIntegral a :=
  integral_turingZetaArgument_eq_horizontal_sub_of_continuous (by norm_num) ha le_rfl (by simp)

example : |∫ T in (1 : ℝ)..1, turingZetaArgument 2 T| ≤ (19 / 2 : ℝ) * Real.log 5 + 95 := by
  simpa using abs_integral_turingZetaArgument_le_of_continuous
    (σ := 2) (a := 1) (b := 1) (by norm_num) le_rfl le_rfl (by simp)

end

end PrimeFactorUnimodality.Tests
