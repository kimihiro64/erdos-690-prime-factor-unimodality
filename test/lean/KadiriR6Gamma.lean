import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Gamma

/-! # Height-uniform R6 interfaces, boundaries and actual consumers -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example {T : ℝ} (hT : 25000000 ≤ T) :
    mossinghoffTrudgianCoefficient 0 * (log 2 - log π) +
      (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i *
        (log ((i : ℝ) / 2 + 2 / T) - log π)) ≤ -(149 / 100 : ℝ) := by
  exact PrimeFactorUnimodality.kadiriSix_gamma_log_sum_le hT

example :
    (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i / (i : ℝ)) ≤ 4 := by
  exact PrimeFactorUnimodality.kadiriSix_reciprocal_mass_le

example {T σ : ℝ} (hT : 25000000 ≤ T) (hσ : 9922 / 10000 ≤ σ) :
    kadiriGammaResidual (437 / 1000) σ T (range 17)
      mossinghoffTrudgianCoefficient ≤ -(1 / 4 : ℝ) := by
  exact PrimeFactorUnimodality.kadiriSix_gamma_residual_le hT hσ

example : kadiriGammaResidual (437 / 1000) (9922 / 10000) 25000000 (range 17)
    mossinghoffTrudgianCoefficient ≤ -(1 / 4 : ℝ) :=
  kadiriSix_gamma_residual_le le_rfl le_rfl

end

end PrimeFactorUnimodality.Tests
