import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Parameters

/-! # Exact statement regressions for the endpoint bootstrap increment -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example {r : ℝ} (hr : 6 ≤ r) :
    0 < KadiriEndpointRow.scale r 1000000000 ∧
      KadiriEndpointRow.scale r 1000000000 ≤ (81 / 10000 : ℝ) := by
  apply PrimeFactorUnimodality.kadiriSix_scale_bounds <;> assumption

example {R : ℝ} (hR : 13 / 2 ≤ R) :
    (9933 / 10000 : ℝ) ≤ kadiriSixRow.sigma R 1000000000 16 ∧
      kadiriSixRow.sigma R 1000000000 16 ≤ 1 := by
  apply PrimeFactorUnimodality.kadiriSix_sigma_bounds <;> assumption

example {η σ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 81 / 10000)
    (hσ : 9933 / 10000 ≤ σ)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0)
    (hg' : kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ)) :
    (439 / 1000 : ℝ) ≤ kadiriKappa₂ (185573 / 100000) η (2 * σ - 1) (62 / 100) ∧
      (439 / 1000 : ℝ) ≤ kadiriKappa₃ (185573 / 100000) η (2 * σ - 1) (62 / 100) := by
  apply PrimeFactorUnimodality.kadiriSix_kappa_bounds <;> assumption

example {R r : ℝ} (hR : 13 / 2 ≤ R) (hr : 6 ≤ r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hcor : kadiriSixRow.correction R r 1000000000 16 mossinghoffTrudgianCoefficient ≤ 0)
    (hlo : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (Finset.range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1)
          (kadiriBootstrapLowerArgument R r 16 100000 1000000000))
    (hhi : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (Finset.range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) 1) :
    kadiriSixRow.Valid R r 1000000000 16 mossinghoffTrudgianCoefficient := by
  apply PrimeFactorUnimodality.kadiriSix_valid <;> assumption

end PrimeFactorUnimodality.Tests
