import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredBootstrap
import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6FourPoints

/-! # Exact statements for the uniform numerical-region correction -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example {R r l b : ℝ}
    (hR : 13 / 2 ≤ R) (hr : 6 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((20718 / 1000) / (47 / 2))) (hb : 138 ≤ b * r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hlo : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) l)
    (hhi : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) 1) :
    kadiriSixRow.Valid R r 1000000000 16 mossinghoffTrudgianCoefficient := by
  apply PrimeFactorUnimodality.kadiriSix_valid_of_rational_points <;> assumption

example
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6 := by
  apply PrimeFactorUnimodality.kadiriSix_chain_of_four_points <;> assumption

example : Fintype.card (Fin 4) = 4 := by simp

example : kadiriSixTransformRow 0 = (3 / 25, 18) ∧
    kadiriSixTransformRow 1 = (71 / 100, 22) ∧
    kadiriSixTransformRow 2 = (81 / 100, 23) ∧
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

end PrimeFactorUnimodality.Tests
