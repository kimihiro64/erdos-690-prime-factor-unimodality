import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogInterchange

/-! # Exact interfaces and boundary cases for the actual logarithmic-ratio chain -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set

example (T : ℝ) (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ turingXiLogAtom T p x := by
  exact PrimeFactorUnimodality.turingXiLogAtom_nonneg T p hx

example (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    (∫ x in Ioc (0 : ℝ) 1, ‖turingXiLogAtom T p x‖) = turingXiLogStep T p := by
  exact PrimeFactorUnimodality.integral_norm_turingXiLogAtom T p

example (T : ℝ) :
    Summable (fun p => ∫ x in Ioc (0 : ℝ) 1, ‖turingXiLogAtom T p x‖) := by
  exact PrimeFactorUnimodality.summable_integral_norm_turingXiLogAtom T

example (T : ℝ) :
    IntervalIntegrable (fun x => ∑' p, turingXiLogAtom T p x) volume 0 1 := by
  exact PrimeFactorUnimodality.intervalIntegrable_tsum_turingXiLogAtom T

example (T : ℝ) :
    (∫ x in (0 : ℝ)..1, ∑' p, turingXiLogAtom T p x) = ∑' p, turingXiLogStep T p := by
  exact PrimeFactorUnimodality.integral_tsum_turingXiLogAtom T

example (p : RiemannXiDivisorZeroIndex) :
    IntervalIntegrable (fun x => ∑' q, turingXiLogAtom (riemannXiDivisorZeroValue p).im q x)
      volume 0 1 := intervalIntegrable_tsum_turingXiLogAtom _

example : (∫ x in (0 : ℝ)..1, ∑' p, turingXiLogAtom 0 p x) =
    ∑' p, turingXiLogStep 0 p := integral_tsum_turingXiLogAtom 0

end

end PrimeFactorUnimodality.Tests
