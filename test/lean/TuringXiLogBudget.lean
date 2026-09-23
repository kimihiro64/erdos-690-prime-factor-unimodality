import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogBudget

/-! # Exact interfaces and boundary cases for TuringXiLogBudget -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory

example (T : ℝ) : (logDeriv riemannXi ((3 / 2 : ℂ) + T * I)).re ≤
    (1 / 2 : ℝ) * Real.log (|T| / 2 + 3) + 11 / 2 :=
  re_logDeriv_riemannXi_three_halves_le T

example (T : ℝ) : (∑' p, turingXiLogStep T p) ≤
    8 * Real.log (|T| / 2 + 3) + 88 := tsum_turingXiLogStep_le_explicit T

example : (∑' p, turingXiLogStep 0 p) ≤ 8 * Real.log 3 + 88 := by
  simpa using tsum_turingXiLogStep_le_explicit 0

example (T : ℝ) : (∑' p, turingXiLogStep (-T) p) ≤
    8 * Real.log (|T| / 2 + 3) + 88 := by
  simpa using tsum_turingXiLogStep_le_explicit (-T)

example (p : RiemannXiDivisorZeroIndex) :
    (∑' q, turingXiLogStep (riemannXiDivisorZeroValue p).im q) ≤
      8 * Real.log (|(riemannXiDivisorZeroValue p).im| / 2 + 3) + 88 :=
  tsum_turingXiLogStep_le_explicit _

end

end PrimeFactorUnimodality.Tests
