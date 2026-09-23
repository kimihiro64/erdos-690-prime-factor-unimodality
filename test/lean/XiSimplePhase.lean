import PrimeFactorUnimodality.Helpers.Analytic.XiSimplePhase

/-! # Checked elementary xi-phase interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open PrimeFactorUnimodality

example {t : ℝ} (ht : 0 < t) :
    |turingStirlingPhase t - xiSimplePhase t| ≤ 33 / (16 * t) := by
  exact PrimeFactorUnimodality.abs_turingStirlingPhase_sub_simple_le ht

example {t : ℝ} (ht : 0 < t) :
    |turingCountingPhase t - xiSimplePhase t| ≤ 1 / 10 + 33 / (16 * t) := by
  exact PrimeFactorUnimodality.abs_turingCountingPhase_sub_simple_le ht

example : |turingStirlingPhase 16 - xiSimplePhase 16| ≤ 33 / 256 := by
  convert abs_turingStirlingPhase_sub_simple_le (t := 16) (by norm_num) using 1 <;> norm_num
example {t : ℝ} (ht : 100 ≤ t) : |turingStirlingPhase t - xiSimplePhase t| ≤ 33 / 1600 := by
  apply (abs_turingStirlingPhase_sub_simple_le (by linarith : 0 < t)).trans
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

end

end PrimeFactorUnimodality.Tests
