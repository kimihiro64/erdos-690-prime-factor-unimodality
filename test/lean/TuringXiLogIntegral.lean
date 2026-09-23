import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogIntegral

/-! # Exact interfaces and boundary cases for the actual logarithmic-ratio chain -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set

example (a T : ℝ) :
    ∀ᵐ x : ℝ, riemannXi ((x : ℂ) + (a : ℂ) + T * I) ≠ 0 := by
  exact PrimeFactorUnimodality.ae_riemannXi_horizontal_ne_zero a T

example (T : ℝ) :
    turingXiLogIncrement T =ᵐ[volume] (fun x => ∑' p, turingXiLogAtom T p x) := by
  exact PrimeFactorUnimodality.ae_turingXiLogIncrement_eq_tsum T

example (T : ℝ) :
    IntervalIntegrable (turingXiLogIncrement T) volume 0 1 := by
  exact PrimeFactorUnimodality.intervalIntegrable_turingXiLogIncrement T

example (T : ℝ) :
    (∫ x in (0 : ℝ)..1, turingXiLogIncrement T x) = ∑' p, turingXiLogStep T p := by
  exact PrimeFactorUnimodality.integral_turingXiLogIncrement_eq_tsum T

example (T : ℝ) :
    (∫ x in (0 : ℝ)..1, turingXiLogIncrement T x) ≤
      8 * Real.log (|T| / 2 + 3) + 88 := by
  exact PrimeFactorUnimodality.integral_turingXiLogIncrement_le T

example (p : RiemannXiDivisorZeroIndex) :
    IntervalIntegrable (turingXiLogIncrement (riemannXiDivisorZeroValue p).im) volume 0 1 :=
  intervalIntegrable_turingXiLogIncrement _

example : (∫ x in (0 : ℝ)..1, turingXiLogIncrement 0 x) ≤ 8 * Real.log 3 + 88 := by
  simpa using integral_turingXiLogIncrement_le 0

example (T : ℝ) : (∫ x in (0 : ℝ)..1, turingXiLogIncrement (-T) x) ≤
    8 * Real.log (|T| / 2 + 3) + 88 := by
  simpa using integral_turingXiLogIncrement_le (-T)

end

end PrimeFactorUnimodality.Tests
