import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Gamma

/-! # Exact statements for the uniform numerical-region correction -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example :
    mossinghoffTrudgianCoefficient 0 * (log 2 - log π) +
      (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i *
        (log ((i : ℝ) / 2 + 2 / 1000000000) - log π)) ≤ -(149 / 100 : ℝ) := by
  apply PrimeFactorUnimodality.kadiriSix_gamma_log_sum_le <;> assumption

example :
    (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i / (i : ℝ)) ≤ 4 := by
  apply PrimeFactorUnimodality.kadiriSix_reciprocal_mass_le <;> assumption

example {σ : ℝ} (hσ : 9933 / 10000 ≤ σ) :
    kadiriGammaResidual (439 / 1000) σ 1000000000 (range 17)
      mossinghoffTrudgianCoefficient ≤ -(1 / 4 : ℝ) := by
  apply PrimeFactorUnimodality.kadiriSix_gamma_residual_le <;> assumption

example : kadiriGammaResidual (439 / 1000) (9933 / 10000) 1000000000 (range 17)
    mossinghoffTrudgianCoefficient ≤ -(1 / 4 : ℝ) :=
  kadiriSix_gamma_residual_le le_rfl

end PrimeFactorUnimodality.Tests
