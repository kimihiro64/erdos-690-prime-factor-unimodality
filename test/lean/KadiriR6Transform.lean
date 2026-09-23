import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Transform

/-! # Exact statements for the uniform numerical-region correction -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example : log (16 * 1000000000 + 100000 : ℝ) ≤ 47 / 2 := by
  apply PrimeFactorUnimodality.kadiriSix_cutoff_log_le <;> assumption

example {R r l : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((20718 / 1000) / (47 / 2))) :
    kadiriBootstrapLowerArgument R r 16 100000 1000000000 ∈ Set.Icc l 1 := by
  apply PrimeFactorUnimodality.kadiriSix_argument_mem <;> assumption

example :
    kadiriBootstrapLowerArgument 56 8 16 100000 1000000000 ∈ Set.Icc (12 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument 8 (13 / 2) 16 100000 1000000000 ∈
        Set.Icc (71 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument (13 / 2) 6 16 100000 1000000000 ∈
        Set.Icc (81 / 100 : ℝ) 1 := by
  apply PrimeFactorUnimodality.kadiriSix_three_argument_intervals <;> assumption

example
    (hg : kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ)) :
    kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (range 17) mossinghoffTrudgianCoefficient ≤ 138 := by
  apply PrimeFactorUnimodality.kadiriSix_log_coefficient_le <;> assumption

example (w : ℝ) :
    kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) w ≤
      kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) w := by
  apply PrimeFactorUnimodality.kadiriSix_rounded_gap_le <;> assumption

example {b l w : ℝ} (hw : w ∈ Set.Icc l 1)
    (hlo : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) l)
    (hhi : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) 1) :
    b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) w := by
  apply PrimeFactorUnimodality.kadiriSix_gap_le_of_rounded_endpoints <;> assumption

end PrimeFactorUnimodality.Tests
