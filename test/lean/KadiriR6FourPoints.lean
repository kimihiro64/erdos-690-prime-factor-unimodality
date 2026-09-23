import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredBootstrap
import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6FourPoints

/-! # Height-uniform R6 interfaces, boundaries and actual consumers -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example {T R r l b : ℝ} (hT : 25000000 ≤ T)
    (hR : 13 / 2 ≤ R) (hr : 6 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((17034 / 1000) / (991 / 50))) (hb : 138 ≤ b * r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hlo : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) l)
    (hhi : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) 1) :
    kadiriSixRow.Valid R r T 16 mossinghoffTrudgianCoefficient := by
  exact PrimeFactorUnimodality.kadiriSix_valid_of_rational_points hT hR hr hrR hl hb hg hm hd he hlo hhi

example {T R : ℝ}
    (hT : 25000000 ≤ T) (hR₀ : 8 ≤ R) (hR₁ : R ≤ 69)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient T R 6 := by
  exact PrimeFactorUnimodality.kadiriSix_chain_of_four_points_from hT hR₀ hR₁ hg hm hd he hpoints

example
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6 := by
  exact PrimeFactorUnimodality.kadiriSix_chain_of_four_points hg hm hd he hpoints

example
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 25000000 69 6 := by
  exact PrimeFactorUnimodality.kadiriSix_reduced_chain_of_four_points hg hm hd he hpoints

example : Fintype.card (Fin 4) = 4 := by simp

example : kadiriSixTransformRow 0 = (9 / 100, 18) ∧
    kadiriSixTransformRow 1 = (69 / 100, 22) ∧
    kadiriSixTransformRow 2 = (79 / 100, 23) ∧
    kadiriSixTransformRow 3 = (1, 23) := by
  norm_num [kadiriSixTransformRow]

example : Function.Injective (fun i => (kadiriSixTransformRow i).1) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | rfl | norm_num [kadiriSixTransformRow] at hij

example : ∀ i : Fin 4, 0 < (kadiriSixTransformRow i).1 ∧
    (kadiriSixTransformRow i).1 ≤ 1 ∧ 18 ≤ (kadiriSixTransformRow i).2 := by
  intro i
  fin_cases i <;> norm_num [kadiriSixTransformRow]

example (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 :=
  hasThetaLogSquaredError_above_endpoint_of_bootstrap
    (kadiriSix_chain_of_four_points hg hm hd he hpoints) hlow

example (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds)
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_lower_band_and_bootstrap finite
    (kadiriSix_chain_of_four_points hg hm hd he hpoints) hlow

end

end PrimeFactorUnimodality.Tests
