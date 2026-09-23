import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffScalars

/-! # Earlier analytic cutoff interfaces and seam regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example : (1151 / 100 : ℝ) ≤ log 100000 ∧
    log 100000 ≤ (2303 / 200 : ℝ) := by
  exact PrimeFactorUnimodality.dusart_log_early_inner_bounds

example :
    xiReciprocalNormWindowBound 25 100000 ≤ (83 / 10 : ℝ) := by
  exact PrimeFactorUnimodality.xiReciprocalNormWindowBound_early_le

example :
    xiLowReciprocalNormBound 25 100000 (1 / 2) ≤ (91 / 5 : ℝ) := by
  exact PrimeFactorUnimodality.xiLowReciprocalNormBound_early_le

example :
    xiRosserPowerTailBound 4 100000 ≤ (11 / 10 ^ 16 : ℝ) := by
  exact PrimeFactorUnimodality.xiRosserPowerTailBound_four_early_inner_le

example :
    xiRosserPowerTailBound 4 25000000 ≤ (11 / 10 ^ 23 : ℝ) := by
  exact PrimeFactorUnimodality.xiRosserPowerTailBound_four_early_outer_le



end

end PrimeFactorUnimodality.Tests
