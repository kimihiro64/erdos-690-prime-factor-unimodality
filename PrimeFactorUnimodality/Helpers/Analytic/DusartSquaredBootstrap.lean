import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAnalyticRay
import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Bootstrap

/-! # Connect the finite bootstrap chain to the actual log-square theta bound

The quantitative high region is now derived from checked endpoint rows and
the proved initial region. The low-height critical-line verification and
lower theta band remain explicit independent obligations. A chain input
is not a claim that its endpoint inequalities have already been certified.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The full analytic ray needs a finite endpoint chain instead of an assumed high region. -/
theorem hasThetaLogSquaredError_above_endpoint_of_bootstrap
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  apply hasThetaLogSquaredError_above_endpoint hlow
  intro z hz
  linarith [xi_zero_gap_six_of_endpoint_chain hchain hlow z hz]

/-- The exact coefficient at the published cutoff keeps only the two finite analytic inputs. -/
theorem hasThetaLogSquaredError_of_lower_band_and_bootstrap
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  apply hasThetaLogSquaredError_of_lower_band_and_zero_data finite hlow
  intro z hz
  linarith [xi_zero_gap_six_of_endpoint_chain hchain hlow z hz]

end

end PrimeFactorUnimodality
