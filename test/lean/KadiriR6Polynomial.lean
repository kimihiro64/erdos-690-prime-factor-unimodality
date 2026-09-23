import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Polynomial

/-! # Height-uniform R6 interfaces, boundaries and actual consumers -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ)) :
    kadiriMomentMassBound (-1)
      (kadiriDerivativeMomentElementary (185573 / 100000) 0)
      (kadiriDerivativeMomentElementary (185573 / 100000) 1)
      (kadiriDerivativeMomentElementary (185573 / 100000) 2)
      (kadiriDerivativeMomentElementary (185573 / 100000) 3) ≤ 3000 := by
  exact PrimeFactorUnimodality.kadiriSix_moment_mass_le hm hd

example {η σ M P L₀ L₁ G q : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 98 / 10000) (hσ : 9922 / 10000 ≤ σ)
    (hM' : M ≤ 3000) (hP : 0 ≤ P) (hP' : P ≤ 1 / 1000)
    (hL₀ : 0 ≤ L₀) (hL₀' : L₀ ≤ 1) (hL₁ : 0 ≤ L₁) (hL₁' : L₁ ≤ 1 / 1000)
    (hG : G ≤ -(1 / 4)) (hq : 0 ≤ q) (hq' : q ≤ 1 / 6)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0)
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ)) :
    kadiriCorrectionPolynomial (185573 / 100000) η η σ (437 / 1000) (62 / 100)
      M P L₀ L₁ G q (range 17) mossinghoffTrudgianCoefficient ≤ 0 := by
  exact PrimeFactorUnimodality.kadiriSix_polynomial_nonpos hη hη' hσ hM' hP hP' hL₀ hL₀' hL₁ hL₁' hG hq hq' hg hm

example (σ M P L₀ L₁ G q : ℝ) :
    kadiriCorrectionPolynomial (185573 / 100000) 0 0 σ (437 / 1000) (62 / 100)
      M P L₀ L₁ G q (range 17) mossinghoffTrudgianCoefficient = 0 := by
  simp [kadiriCorrectionPolynomial]

end

end PrimeFactorUnimodality.Tests
