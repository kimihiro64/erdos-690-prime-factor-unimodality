import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformChecks
import PrimeFactorUnimodality.Helpers.FiniteCertificates.KadiriKernelNumerical

/-! # Checked four-point transforms and the complete R6 endpoint chains

All four rational rows use the same expression semantics and checked dyadic
evaluator. The zero exponent in the upper endpoint is handled exactly.
The kernel bounds are imported once rather than replayed. These closed
chains discharge numerical bootstrap premises, not low-height zero data.
-/

namespace PrimeFactorUnimodality

set_option maxRecDepth 4000

private theorem transform_rows_checked :
    ∀ i : Fin 4, checkKadiriSixTransformRow i (-40) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

/-- Every required rational transform lower bound is certified by the kernel. -/
theorem kadiriSix_transform_bounds : KadiriSixTransformBounds :=
  kadiriSixTransformBounds_of_checks (-40) 16 (by norm_num) transform_rows_checked

/-- The same checked finite data supplies the full height-uniform chain. -/
theorem kadiriSix_endpoint_chain_from {T R : ℝ}
    (hT : 25000000 ≤ T) (hR₀ : 8 ≤ R) (hR₁ : R ≤ 69) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient T R 6 :=
  kadiriSix_chain_of_four_points_from hT hR₀ hR₁
    mossinghoffTrudgian_kernel_zero_bounds mossinghoffTrudgian_kernel_second_le
    mossinghoffTrudgian_support_le mossinghoffTrudgian_support_exp_le kadiriSix_transform_bounds

/-- The billion-height chain has no remaining scalar-transform premise. -/
theorem kadiriSix_endpoint_chain :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6 :=
  kadiriSix_endpoint_chain_from (by norm_num) (by norm_num) (by norm_num)

/-- The reduced-height psi route uses the same certified scalar data. -/
theorem kadiriSix_reduced_endpoint_chain :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 25000000 69 6 :=
  kadiriSix_endpoint_chain_from (by norm_num) (by norm_num) (by norm_num)

end PrimeFactorUnimodality
