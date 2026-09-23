import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Tail

/-! # Height-uniform R6 interfaces, boundaries and actual consumers -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example {T : ℝ} (hT : 25000000 ≤ T) :
    xiLehmanLogCoefficient T 100000 ≤ (1 / 100000 : ℝ) := by
  exact PrimeFactorUnimodality.kadiriSix_lehman_log_coefficient_le hT

example {T : ℝ} (hT : 25000000 ≤ T) :
    xiLehmanAffineConstant T 100000 ≤ (1 / 100000 : ℝ) := by
  exact PrimeFactorUnimodality.kadiriSix_lehman_affine_constant_le hT

example {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriPoleCoefficient (range 17) mossinghoffTrudgianCoefficient T ≤
      (1 / 1000 : ℝ) := by
  exact PrimeFactorUnimodality.kadiriSix_pole_coefficient_le hT

example {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriTailLogCoefficient T 100000 (range 17) mossinghoffTrudgianCoefficient ≤
      (1 / 1000 : ℝ) := by
  exact PrimeFactorUnimodality.kadiriSix_tail_log_coefficient_le hT

example {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriTailConservativeConstant T 100000 (range 17)
      mossinghoffTrudgianCoefficient ≤ 1 := by
  exact PrimeFactorUnimodality.kadiriSix_tail_constant_le hT



end

end PrimeFactorUnimodality.Tests
