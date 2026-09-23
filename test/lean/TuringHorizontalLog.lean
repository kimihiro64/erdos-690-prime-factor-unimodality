import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalLog

/-! # Exact interfaces and boundary tests for horizontal zeta logarithms -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex LSeries

open ArithmeticFunction

open MeasureTheory Set

example {T : ℝ} (hT : T ≠ 0) :
    IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖)
      (Ioi (1 / 2 : ℝ)) := by
  exact PrimeFactorUnimodality.integrableOn_turingHorizontalLog hT

example {T c : ℝ} (hT : T ≠ 0) (hc : 1 < c) :
    turingHorizontalIntegral T =
      (∫ x in (1 / 2 : ℝ)..c, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) +
        ∫ x in Ioi c, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ := by
  exact PrimeFactorUnimodality.turingHorizontalIntegral_eq_split hT hc

example {x T : ℝ}
    (hT : 1 ≤ |T|) (hx : 1 / 2 ≤ x) :
    ‖riemannZeta ((x : ℂ) + T * I)‖ ≤ 5 * |T| := by
  exact PrimeFactorUnimodality.norm_riemannZeta_horizontal_le_five_height hT hx

example {x T : ℝ}
    (hT : 1 ≤ |T|) (hx : 1 / 2 ≤ x) :
    Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ ≤ Real.log (5 * |T|) := by
  exact PrimeFactorUnimodality.log_norm_riemannZeta_horizontal_le hT hx

example (T : ℝ) :
    |∫ x in Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + T * I)‖| ≤ 1 := by
  exact PrimeFactorUnimodality.abs_integral_turingHorizontalLog_tail_two_le_one T

example {T : ℝ} (hT : 1 ≤ |T|) :
    turingHorizontalIntegral T ≤ (3 / 2 : ℝ) * Real.log (5 * |T|) + 1 := by
  exact PrimeFactorUnimodality.turingHorizontalIntegral_le hT


example : turingHorizontalIntegral 1 ≤ (3 / 2 : ℝ) * Real.log 5 + 1 := by
  simpa using turingHorizontalIntegral_le (T := 1) (by norm_num)

example : turingHorizontalIntegral (-1) ≤ (3 / 2 : ℝ) * Real.log 5 + 1 := by
  simpa using turingHorizontalIntegral_le (T := -1) (by norm_num)

example : |∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta (x : ℂ)‖| ≤ 1 := by
  simpa using abs_integral_turingHorizontalLog_tail_two_le_one 0

end

end PrimeFactorUnimodality.Tests
