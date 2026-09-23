import PrimeFactorUnimodality.Helpers.FiniteCertificates.KadiriTransformNumerical

/-! # Exact R6 interfaces and branch regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core

example : KadiriSixTransformBounds := by
  exact PrimeFactorUnimodality.kadiriSix_transform_bounds

example {T R : ℝ}
    (hT : 25000000 ≤ T) (hR₀ : 8 ≤ R) (hR₁ : R ≤ 69) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient T R 6 := by
  exact PrimeFactorUnimodality.kadiriSix_endpoint_chain_from hT hR₀ hR₁

example :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6 := by
  exact PrimeFactorUnimodality.kadiriSix_endpoint_chain

example :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 25000000 69 6 := by
  exact PrimeFactorUnimodality.kadiriSix_reduced_endpoint_chain

example : (18 : ℝ) ≤ kadiriTransformGapClosedForm (185573 / 100000) 1
    (1741 / 1000) (9 / 100) := by
  simpa [kadiriSixTransformRow] using kadiriSix_transform_bounds 0

example : (22 : ℝ) ≤ kadiriTransformGapClosedForm (185573 / 100000) 1
    (1741 / 1000) (69 / 100) := by
  simpa [kadiriSixTransformRow] using kadiriSix_transform_bounds 1

example : (23 : ℝ) ≤ kadiriTransformGapClosedForm (185573 / 100000) 1
    (1741 / 1000) (79 / 100) := by
  simpa [kadiriSixTransformRow] using kadiriSix_transform_bounds 2

example : (23 : ℝ) ≤ kadiriTransformGapClosedForm (185573 / 100000) 1
    (1741 / 1000) 1 := by
  simpa [kadiriSixTransformRow] using kadiriSix_transform_bounds 3

example : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 25000000 8 6 :=
  kadiriSix_endpoint_chain_from (by norm_num) (by norm_num) (by norm_num)

example : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 69 6 :=
  kadiriSix_endpoint_chain_from (by norm_num) (by norm_num) (by norm_num)

end

end PrimeFactorUnimodality.Tests
