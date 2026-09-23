import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Correction

/-! # Exact statements for the uniform numerical-region correction -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example {R r : ℝ} (hR : 13 / 2 ≤ R) (hr : 6 ≤ r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0)
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ)) :
    kadiriSixRow.correction R r 1000000000 16 mossinghoffTrudgianCoefficient ≤ 0 := by
  apply PrimeFactorUnimodality.kadiriSix_correction_nonpos <;> assumption

example {R r : ℝ} (hR : 13 / 2 ≤ R) (hr : 6 ≤ r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hlo : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1)
          (kadiriBootstrapLowerArgument R r 16 100000 1000000000))
    (hhi : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) 1) :
    kadiriSixRow.Valid R r 1000000000 16 mossinghoffTrudgianCoefficient := by
  apply PrimeFactorUnimodality.kadiriSix_valid_of_transform_margins <;> assumption

end PrimeFactorUnimodality.Tests
