import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogStep

/-! # Exact interfaces and boundary cases for TuringXiLogStep -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory

example (T : ℝ) (p : RiemannXiDivisorZeroIndex) : 0 ≤ turingXiLogStep T p :=
  turingXiLogStep_nonneg T p

example (T : ℝ) : Summable (turingXiLogStep T) := summable_turingXiLogStep T

example (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    turingXiLogStep T p + turingXiLogStep T (riemannXiDivisorSameHeightReflection p) ≤
      16 * ((1 / (((3 / 2 : ℂ) + T * I) - riemannXiDivisorZeroValue p)).re +
        (1 / (((3 / 2 : ℂ) + T * I) -
          riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p))).re) :=
  turingXiLogStep_pair_le T p

example (T : ℝ) : (∑' p, turingXiLogStep T p) ≤
    16 * (logDeriv riemannXi ((3 / 2 : ℂ) + T * I)).re := tsum_turingXiLogStep_le T

example : Summable (turingXiLogStep 0) := summable_turingXiLogStep 0

example : (∑' p, turingXiLogStep 0 p) ≤ 16 * (logDeriv riemannXi (3 / 2 : ℂ)).re := by
  simpa using tsum_turingXiLogStep_le 0

example (p : RiemannXiDivisorZeroIndex) :
    Summable (turingXiLogStep (riemannXiDivisorZeroValue p).im) :=
  summable_turingXiLogStep _

example (T : ℝ) : (∑' p, turingXiLogStep (-T) p) ≤
    16 * (logDeriv riemannXi ((3 / 2 : ℂ) + (-T) * I)).re := by
  simpa using tsum_turingXiLogStep_le (-T)

end

end PrimeFactorUnimodality.Tests
