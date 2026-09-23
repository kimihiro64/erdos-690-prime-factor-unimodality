import PrimeFactorUnimodality.Helpers.Analytic.XiRosserPolynomialTail

/-! # Regression statements for the decreasing logarithmic error -/

namespace PrimeFactorUnimodality.Tests

open Real

example (n : ℕ) {a q U : ℝ}
    (ha : 0 < a) (hq : 3 ≤ q) (hU : 10 < U) :
    xiRosserAbsoluteTail a q U ≤
      ((n.factorial : ℝ) ^ 2 / a ^ n) * xiRosserPowerTailBound (q - 1) U :=
  xiRosserAbsoluteTail_le_polynomial n ha hq hU

end PrimeFactorUnimodality.Tests
