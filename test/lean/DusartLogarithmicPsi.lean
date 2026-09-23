import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicPsi

/-! # Regression statements for the decreasing logarithmic error -/

namespace PrimeFactorUnimodality.Tests

open Real

example {x : ℝ}
    (hx : 1 < x) (hb : 100 ≤ Real.log x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x ≤ (103 / 100 : ℝ) / Real.log x :=
  abs_psi_sub_div_le_logarithmic_of_billion_low_gap hx hb hgap

end PrimeFactorUnimodality.Tests
