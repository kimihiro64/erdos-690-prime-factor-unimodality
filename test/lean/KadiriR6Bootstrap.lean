import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Bootstrap

/-! # Exact statement regressions for the endpoint bootstrap increment -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 1000000000 := by
  apply PrimeFactorUnimodality.xi_zero_gap_six_of_endpoint_chain <;> assumption

example
    (h₁ : kadiriSixRow.Valid 56 8 1000000000 16 mossinghoffTrudgianCoefficient)
    (h₂ : kadiriSixRow.Valid 8 (13 / 2) 1000000000 16 mossinghoffTrudgianCoefficient)
    (h₃ : kadiriSixRow.Valid (13 / 2) 6 1000000000 16 mossinghoffTrudgianCoefficient)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|) := by
  apply PrimeFactorUnimodality.xi_zero_gap_six_of_three_endpoint_rows <;> assumption

end PrimeFactorUnimodality.Tests
