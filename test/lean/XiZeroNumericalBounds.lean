import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds

/-! # Regression checks for explicit endpoint estimates and their hypotheses -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example :
    (2 + eulerMascheroniConstant - Real.log (4 * π)) / 2 <
    (3 / 100 : ℝ) :=
  xiRealReciprocalMass_lt_three_hundredths

example : (2302 / 1000 : ℝ) ≤ Real.log 10 ∧
    Real.log 10 ≤ (2303 / 1000 : ℝ) :=
  dusart_log_ten_bounds

example :
    xiReciprocalNormWindowBound 10 1000000 ≤ (2673 / 200 : ℝ) :=
  xiReciprocalNormWindowBound_million_le

example : xiLowReciprocalNormBound 10 1000000 (1 / 2) ≤
    (561 / 20 : ℝ) :=
  xiLowReciprocalNormBound_million_half_le

example {U : ℝ} (hU : 0 < U) :
    xiRosserPowerTailBound 4 U =
      (3 * Real.log (U / (2 * π)) + 1) / (9 * π * U ^ 3) +
        (4 * Real.log U + 137 / 2) / U ^ 4 :=
  xiRosserPowerTailBound_four_eq hU

example {U L : ℝ} (hU : 0 < U) (hL : 2 ≤ L)
    (hlog : Real.log U ≤ L) :
    xiRosserPowerTailBound 4 U ≤
      (3 * L - 3 * (1837 / 1000 : ℝ) + 1) / (9 * (314 / 100 : ℝ) * U ^ 3) +
        (4 * L + 137 / 2) / U ^ 4 :=
  xiRosserPowerTailBound_four_le_log_bound hU hL hlog

example : xiRosserPowerTailBound 4 1000000 ≤
    (131 / 10 ^ 20 : ℝ) :=
  xiRosserPowerTailBound_four_million_le

example : xiRosserPowerTailBound 4 1000000000 ≤
    (205 / 10 ^ 29 : ℝ) :=
  xiRosserPowerTailBound_four_billion_le

end PrimeFactorUnimodality.Tests
