import PrimeFactorUnimodality.Helpers.Analytic.XiPositiveReciprocalMass

/-! # Reduced-cutoff interfaces and real-endpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real Set MeasureTheory

example (a : ℝ) :
    (∑ p ∈ xiPositiveHeightIndices a, (1 / riemannXiDivisorZeroValue p).re) ≤
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 := by
  exact PrimeFactorUnimodality.sum_xi_positive_reciprocal_le_half_total a

example : (∑ p ∈ xiPositiveHeightIndices 0, (1 / riemannXiDivisorZeroValue p).re) ≤
    (2 + eulerMascheroniConstant - log (4 * π)) / 4 :=
  sum_xi_positive_reciprocal_le_half_total 0

example : (∑ p ∈ xiPositiveHeightIndices (-1), (1 / riemannXiDivisorZeroValue p).re) ≤
    (2 + eulerMascheroniConstant - log (4 * π)) / 4 :=
  sum_xi_positive_reciprocal_le_half_total (-1)

example : (∑ p ∈ xiPositiveHeightIndices 25, (1 / riemannXiDivisorZeroValue p).re) ≤
    (2 + eulerMascheroniConstant - log (4 * π)) / 4 :=
  sum_xi_positive_reciprocal_le_half_total 25

end

end PrimeFactorUnimodality.Tests
