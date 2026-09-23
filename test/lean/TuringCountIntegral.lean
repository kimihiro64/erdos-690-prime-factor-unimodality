import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringCountIntegral

/-! # Exact interfaces and boundary regressions for counting normalization -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Set
open MeasureTheory

example :
    ∀ᵐ T : ℝ, ∀ z : ℂ, z.im = T → riemannXi z ≠ 0 := by
  exact PrimeFactorUnimodality.ae_xi_horizontal_nonzero

example {T : ℝ}
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    xiZeroCount T = xiStrictZeroCount T := by
  exact PrimeFactorUnimodality.xiZeroCount_eq_strict_of_regular htop

example {σ : ℝ} (hσ : 1 < σ) :
    ∀ᵐ T : ℝ, 0 < T →
      turingZetaArgument σ T = Real.pi * (xiZeroCount T : ℝ) - turingCountingPhase T := by
  exact PrimeFactorUnimodality.ae_turingZetaArgument_eq_count_sub_phase hσ

example {σ a b : ℝ} (hσ : 1 < σ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (turingZetaArgument σ) volume a b := by
  exact PrimeFactorUnimodality.intervalIntegrable_turingZetaArgument hσ ha hab

example {σ a b : ℝ} (hσ : 1 < σ)
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ T in a..b, turingZetaArgument σ T) =
      Real.pi * (∫ T in a..b, (xiZeroCount T : ℝ)) - ∫ T in a..b, turingCountingPhase T := by
  exact PrimeFactorUnimodality.integral_turingZetaArgument_eq_count_sub_phase hσ ha hab

example {σ a b : ℝ} (hσ : 1 < σ)
    (ha : 0 < a) (hab : a ≤ b) :
    Real.pi * (∫ T in a..b, xiZeroCountingRemainder T) =
      (∫ T in a..b, turingZetaArgument σ T) + (∫ T in a..b, turingCountingPhase T) -
        Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) := by
  exact PrimeFactorUnimodality.pi_mul_integral_xiZeroCountingRemainder hσ ha hab

example (p : RiemannXiDivisorZeroIndex) (hp : 0 < (riemannXiDivisorZeroValue p).im) :
    IntervalIntegrable (turingZetaArgument 2) volume (riemannXiDivisorZeroValue p).im
      ((riemannXiDivisorZeroValue p).im + 1) :=
  intervalIntegrable_turingZetaArgument (by norm_num) hp (by linarith)

example {a : ℝ} (ha : 0 < a) : Real.pi * (∫ T in a..a, xiZeroCountingRemainder T) =
    (∫ T in a..a, turingZetaArgument 2 T) + (∫ T in a..a, turingCountingPhase T) -
      Real.pi * (xiZeroCountingMainIntegral a - xiZeroCountingMainIntegral a) :=
  pi_mul_integral_xiZeroCountingRemainder (by norm_num) ha le_rfl

end

end PrimeFactorUnimodality.Tests
