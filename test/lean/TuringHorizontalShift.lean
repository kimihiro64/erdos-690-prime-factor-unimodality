import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalShift

/-! # Exact interfaces and boundary tests for horizontal zeta logarithms -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex LSeries

open ArithmeticFunction

open MeasureTheory Set

example {T d : ℝ} (hT : T ≠ 0) (hd : 1 / 2 < d) :
    turingHorizontalIntegral T = turingShiftedLogIntegral d T +
      (∫ x in Ioi (1 / 2 + d), Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) +
      ∫ x in (1 / 2 + d)..(1 / 2 + d + d),
        Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ := by
  exact PrimeFactorUnimodality.turingHorizontalIntegral_eq_shift hT hd

example {T d : ℝ} (hT : T ≠ 0) (hd : 1 / 2 < d) :
    turingShiftedLogIntegral d T -
        2 * (Real.log ‖riemannZeta ((1 / 2 + d : ℝ) : ℂ)‖ / Real.log 2) ≤
      turingHorizontalIntegral T := by
  exact PrimeFactorUnimodality.turingShiftedLogIntegral_sub_budget_le hT hd

example {T : ℝ} (hT : T ≠ 0) :
    turingShiftedLogIntegral 1 T - 4 ≤ turingHorizontalIntegral T := by
  exact PrimeFactorUnimodality.turingShiftedLogIntegral_one_sub_four_le hT


example (T : ℝ) : turingShiftedLogIntegral 0 T = 0 := by
  simp [turingShiftedLogIntegral]

example {T : ℝ} (hT : T ≠ 0) :
    turingHorizontalIntegral T = turingShiftedLogIntegral 1 T +
      (∫ x in Set.Ioi (3 / 2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) +
      ∫ x in (3 / 2 : ℝ)..(5 / 2), Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ := by
  convert turingHorizontalIntegral_eq_shift hT (by norm_num : (1 / 2 : ℝ) < 1) using 1 <;>
    norm_num

example : turingShiftedLogIntegral 1 (-1) - 4 ≤ turingHorizontalIntegral (-1) := by
  exact turingShiftedLogIntegral_one_sub_four_le (by norm_num)

end

end PrimeFactorUnimodality.Tests
