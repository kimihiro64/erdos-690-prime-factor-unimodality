import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Tail

/-! # Exact statements for the uniform numerical-region correction -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example :
    xiLehmanLogCoefficient 1000000000 100000 ≤ (1 / 100000 : ℝ) := by
  apply PrimeFactorUnimodality.kadiriSix_lehman_log_coefficient_le <;> assumption

example :
    xiLehmanAffineConstant 1000000000 100000 ≤ (1 / 100000 : ℝ) := by
  apply PrimeFactorUnimodality.kadiriSix_lehman_affine_constant_le <;> assumption

example :
    kadiriPoleCoefficient (range 17) mossinghoffTrudgianCoefficient 1000000000 ≤
      (1 / 1000 : ℝ) := by
  apply PrimeFactorUnimodality.kadiriSix_pole_coefficient_le <;> assumption

example :
    kadiriTailLogCoefficient 1000000000 100000 (range 17) mossinghoffTrudgianCoefficient ≤
      (1 / 1000 : ℝ) := by
  apply PrimeFactorUnimodality.kadiriSix_tail_log_coefficient_le <;> assumption

example :
    kadiriTailConservativeConstant 1000000000 100000 (range 17)
      mossinghoffTrudgianCoefficient ≤ 1 := by
  apply PrimeFactorUnimodality.kadiriSix_tail_constant_le <;> assumption

end PrimeFactorUnimodality.Tests
