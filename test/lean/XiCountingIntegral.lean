import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiCountingIntegral

/-! # Exact interfaces and endpoint regressions for integrated zero verification -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset MeasureTheory

open XiSignRows

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

example {T : ℝ} (hT : 0 < T) :
    HasDerivAt xiZeroCountingMainIntegral (xiZeroCountingMainTerm T) T := by
  exact PrimeFactorUnimodality.hasDerivAt_xiZeroCountingMainIntegral hT

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable xiZeroCountingMainTerm volume a b := by
  exact PrimeFactorUnimodality.intervalIntegrable_xiZeroCountingMainTerm ha hab

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, xiZeroCountingMainTerm t) =
      xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a := by
  exact PrimeFactorUnimodality.integral_xiZeroCountingMainTerm ha hab

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, xiZeroCountingRemainder t) =
      (∫ t in a..b, (xiZeroCount t : ℝ)) -
        (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) := by
  exact PrimeFactorUnimodality.integral_xiZeroCountingRemainder ha hab


example {a : ℝ} (ha : 0 < a) :
    (∫ t in a..a, xiZeroCountingMainTerm t) = 0 := by
  rw [integral_xiZeroCountingMainTerm ha le_rfl, sub_self]

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in b..a, xiZeroCountingMainTerm t) =
      xiZeroCountingMainIntegral a - xiZeroCountingMainIntegral b := by
  rw [intervalIntegral.integral_symm, integral_xiZeroCountingMainTerm ha hab, neg_sub]

example : xiZeroCountingMainIntegral (2 * Real.pi) = -(3 * Real.pi / 2) := by
  dsimp [xiZeroCountingMainIntegral]
  rw [div_self (by positivity : 2 * Real.pi ≠ 0), Real.log_one, mul_zero, zero_sub]
  field_simp
  ring

end

end PrimeFactorUnimodality.Tests
