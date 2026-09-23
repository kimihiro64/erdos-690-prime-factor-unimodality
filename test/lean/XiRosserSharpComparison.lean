import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSharpComparison

/-! # Regression tests for normalized Rosser estimates -/

namespace PrimeFactorUnimodality.Tests

open Real

example {X m ν : ℝ}
    (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2) :
    xiRosserSharpTailBound X m ν ≤ xiRosserNuTailBound X (m + 1) ν :=
  xiRosserSharpTailBound_le_nu hν hmargin

example {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : (m * Real.log (2 * π) - 1) / sqrt m ≤ X)
    (hT : 10 < exp (ν * X)) :
    xiRosserAbsoluteTail (X ^ 2) (m + 1) (exp (ν * X)) ≤ xiRosserSharpTailBound X m ν :=
  xiRosserAbsoluteTail_le_sharp_of_parameter hX hm hν hmargin hparam hT

end PrimeFactorUnimodality.Tests
