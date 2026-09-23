import PrimeFactorUnimodality.Helpers.Analytic.XiRosserClosedBounds

/-! # Full-power tail bounds without exponent loss at zero damping -/

namespace PrimeFactorUnimodality.Tests

open Real

example {q U : ℝ} (hq : 2 ≤ q) (hU : 10 < U) :
    xiRosserAbsoluteTail 0 q U ≤ xiRosserPowerTailBound q U :=
  xiRosserAbsoluteTail_zero_le_power hq hU

example {U : ℝ} (hU : 10 < U) :
    xiRosserAbsoluteTail 0 2 U ≤ xiRosserPowerTailBound 2 U :=
  xiRosserAbsoluteTail_zero_le_power le_rfl hU

example {U : ℝ} (hU : 10 < U) :
    xiRosserAbsoluteTail 0 4 U ≤ xiRosserPowerTailBound 4 U :=
  xiRosserAbsoluteTail_zero_le_power (by norm_num) hU

end PrimeFactorUnimodality.Tests
