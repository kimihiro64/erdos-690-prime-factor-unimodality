import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiLogRatio

/-! # Exact interfaces and boundary cases for the actual logarithmic-ratio chain -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set

example {z : ℂ} (hz : riemannXi z ≠ 0)
    (hz1 : riemannXi (z + 1) ≠ 0) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      Real.log ‖z + 1 - riemannXiDivisorZeroValue p‖ -
        Real.log ‖z - riemannXiDivisorZeroValue p‖) := by
  exact PrimeFactorUnimodality.summable_xi_log_distance_step hz hz1

example {z : ℂ} (hz : riemannXi z ≠ 0)
    (hz1 : riemannXi (z + 1) ≠ 0) :
    Real.log ‖riemannXi (z + 1)‖ - Real.log ‖riemannXi z‖ =
      ∑' p : RiemannXiDivisorZeroIndex,
        (Real.log ‖z + 1 - riemannXiDivisorZeroValue p‖ -
          Real.log ‖z - riemannXiDivisorZeroValue p‖) := by
  exact PrimeFactorUnimodality.log_norm_riemannXi_step_eq_tsum hz hz1

example : Real.log ‖riemannXi (3 : ℂ)‖ - Real.log ‖riemannXi (2 : ℂ)‖ =
    ∑' p : RiemannXiDivisorZeroIndex,
      (Real.log ‖(3 : ℂ) - riemannXiDivisorZeroValue p‖ -
        Real.log ‖(2 : ℂ) - riemannXiDivisorZeroValue p‖) := by
  simpa only [show (2 : ℂ) + 1 = 3 by norm_num] using log_norm_riemannXi_step_eq_tsum (z := 2)
    (riemannXi_ne_zero_of_one_lt_re (by norm_num))
    (riemannXi_ne_zero_of_one_lt_re (by norm_num))

end

end PrimeFactorUnimodality.Tests
