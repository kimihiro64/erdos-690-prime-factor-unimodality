import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredBootstrap

/-! # The exact theta coefficient and both cutoffs after bootstrap assembly -/

namespace PrimeFactorUnimodality.Tests

example
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 :=
  hasThetaLogSquaredError_above_endpoint_of_bootstrap hchain hlow

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_lower_band_and_bootstrap finite hchain hlow

end PrimeFactorUnimodality.Tests
