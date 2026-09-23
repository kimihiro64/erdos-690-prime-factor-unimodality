import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiStirlingPhase

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example (t : ℝ) :
    |turingCountingPhase t - turingStirlingPhase t| ≤ 1 / 10 := by
  exact PrimeFactorUnimodality.abs_turingCountingPhase_sub_stirling_le t

example {t ε : ℝ} {w : ℂ}
    (hw : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ ε) :
    |xiNormalizedValue t - (exp (I * turingStirlingPhase t) * w).re| ≤
      ε + ‖w‖ / 10 := by
  exact PrimeFactorUnimodality.abs_xiNormalizedValue_sub_stirlingApprox_le hw

example : |turingCountingPhase 0 - turingStirlingPhase 0| ≤ 1 / 10 :=
  abs_turingCountingPhase_sub_stirling_le 0

example : |turingCountingPhase (-100) - turingStirlingPhase (-100)| ≤ 1 / 10 :=
  abs_turingCountingPhase_sub_stirling_le (-100)

end

end PrimeFactorUnimodality.Tests
