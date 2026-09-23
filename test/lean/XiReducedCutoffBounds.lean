import PrimeFactorUnimodality.Helpers.Analytic.XiReducedCutoffBounds

/-! # Reduced-cutoff interfaces and real-endpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real Set MeasureTheory

example {a U : ℝ} (ha : 0 < a) (hU : 0 < U) :
    xiReciprocalNormWindowBound a U =
      (log U ^ 2 - log a ^ 2 - 2 * log (2 * π) * (log U - log a) +
        2 * log a - 2 * log (2 * π) - 2) / (4 * π) + (log a + 18) / a - 1 / U := by
  exact PrimeFactorUnimodality.xiReciprocalNormWindowBound_eq_logs ha hU

example : (3218 / 1000 : ℝ) ≤ log 25 ∧
    log 25 ≤ (3219 / 1000 : ℝ) := by
  exact PrimeFactorUnimodality.dusart_log_twenty_five_bounds

example : (14038 / 1000 : ℝ) ≤ log 1250000 ∧
    log 1250000 ≤ (14039 / 1000 : ℝ) := by
  exact PrimeFactorUnimodality.dusart_log_inner_reduced_bounds

example : (17034 / 1000 : ℝ) ≤ log 25000000 ∧
    log (25000000 : ℝ) ≤ 17035 / 1000 := by
  exact PrimeFactorUnimodality.dusart_log_outer_reduced_bounds

example :
    xiReciprocalNormWindowBound 25 1250000 ≤ (12613 / 1000 : ℝ) := by
  exact PrimeFactorUnimodality.xiReciprocalNormWindowBound_reduced_le

example :
    xiLowReciprocalNormBound 25 1250000 (1 / 2) ≤ (13393 / 500 : ℝ) := by
  exact PrimeFactorUnimodality.xiLowReciprocalNormBound_reduced_le

example {U : ℝ} (hU : 0 < U) :
    xiRosserPowerTailBound 6 U =
      (5 * log (U / (2 * π)) + 1) / (25 * π * U ^ 5) +
        (4 * log U + 205 / 3) / U ^ 6 := by
  exact PrimeFactorUnimodality.xiRosserPowerTailBound_six_eq hU

example {U L : ℝ} (hU : 0 < U)
    (hL : 2 ≤ L) (hlog : log U ≤ L) :
    xiRosserPowerTailBound 6 U ≤
      (5 * L - 5 * (1837 / 1000 : ℝ) + 1) / (25 * (314 / 100 : ℝ) * U ^ 5) +
        (4 * L + 205 / 3) / U ^ 6 := by
  exact PrimeFactorUnimodality.xiRosserPowerTailBound_six_le_log_bound hU hL hlog

example :
    xiRosserPowerTailBound 6 1250000 ≤ (26 / 10 ^ 32 : ℝ) := by
  exact PrimeFactorUnimodality.xiRosserPowerTailBound_six_inner_reduced_le

example :
    xiRosserPowerTailBound 6 25000000 ≤ (102 / 10 ^ 39 : ℝ) := by
  exact PrimeFactorUnimodality.xiRosserPowerTailBound_six_outer_reduced_le



end

end PrimeFactorUnimodality.Tests
