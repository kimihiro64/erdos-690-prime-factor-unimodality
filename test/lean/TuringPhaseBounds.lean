import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringPhaseBounds

/-! # Exact interfaces and endpoint cases for the proved Turing counting budget -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Set
open MeasureTheory

example {T : ℝ} (hT : 0 < T) :
    turingCountingPhase T - Real.pi * xiZeroCountingMainTerm T ≤
      7 * Real.pi / 8 + 1 / 10 + 33 / (16 * T) := by
  exact PrimeFactorUnimodality.turingCountingPhase_sub_main_le hT

example {T : ℝ} (hT : 32 ≤ T) :
    turingCountingPhase T - Real.pi * xiZeroCountingMainTerm T ≤ (15 / 16 : ℝ) * Real.pi := by
  exact PrimeFactorUnimodality.turingCountingPhase_sub_main_le_fifteen_sixteenths hT

example : turingCountingPhase 32 - Real.pi * xiZeroCountingMainTerm 32 ≤
    (15 / 16 : ℝ) * Real.pi :=
  turingCountingPhase_sub_main_le_fifteen_sixteenths le_rfl

example : turingCountingPhase 1 - Real.pi * xiZeroCountingMainTerm 1 ≤
    7 * Real.pi / 8 + 1 / 10 + 33 / 16 := by
  simpa using turingCountingPhase_sub_main_le (T := 1) (by norm_num)

end

end PrimeFactorUnimodality.Tests
