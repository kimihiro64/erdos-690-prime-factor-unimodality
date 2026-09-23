import PrimeFactorUnimodality.Helpers.FiniteCertificates.KadiriKernelNumerical

/-! # Exact statement regressions for the endpoint bootstrap increment -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ) := by
  apply PrimeFactorUnimodality.mossinghoffTrudgian_support_le <;> assumption

example :
    (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ) := by
  apply PrimeFactorUnimodality.mossinghoffTrudgian_kernel_zero_bounds <;> assumption

example :
    -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ) := by
  apply PrimeFactorUnimodality.mossinghoffTrudgian_kernel_second_le <;> assumption

example :
    exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100) := by
  apply PrimeFactorUnimodality.mossinghoffTrudgian_support_exp_le <;> assumption

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) :
    -kadiriKernel₂ θ 0 = (1 + tan θ ^ 2) * tan θ ^ 2 *
      ((1 + tan θ ^ 2) * kadiriSupport θ / 2 + 1) := neg_kadiriKernel₂_zero hθ

end PrimeFactorUnimodality.Tests
