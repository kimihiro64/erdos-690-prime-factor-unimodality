import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Transform

/-! # Height-uniform R6 interfaces, boundaries and actual consumers -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example : log (16 * 25000000 + 100000 : ℝ) ≤ 991 / 50 := by
  exact PrimeFactorUnimodality.kadiriSix_cutoff_log_le

example {T R r l : ℝ} (hT : 25000000 ≤ T)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((17034 / 1000) / (991 / 50))) :
    kadiriBootstrapLowerArgument R r 16 100000 T ∈ Set.Icc l 1 := by
  exact PrimeFactorUnimodality.kadiriSix_argument_mem hT hR hr hrR hl

example {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriBootstrapLowerArgument 69 8 16 100000 T ∈ Set.Icc (9 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument 8 (13 / 2) 16 100000 T ∈
        Set.Icc (69 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument (13 / 2) 6 16 100000 T ∈
        Set.Icc (79 / 100 : ℝ) 1 := by
  exact PrimeFactorUnimodality.kadiriSix_three_argument_intervals hT

example
    (hg : kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ)) :
    kadiriBootstrapLogCoefficient (185573 / 100000) (437 / 1000)
      (range 17) mossinghoffTrudgianCoefficient ≤ 138 := by
  exact PrimeFactorUnimodality.kadiriSix_log_coefficient_le hg

example (w : ℝ) :
    kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) w ≤
      kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) w := by
  exact PrimeFactorUnimodality.kadiriSix_rounded_gap_le w

example {b l w : ℝ} (hw : w ∈ Set.Icc l 1)
    (hlo : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) l)
    (hhi : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) 1) :
    b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) w := by
  exact PrimeFactorUnimodality.kadiriSix_gap_le_of_rounded_endpoints hw hlo hhi

example : kadiriBootstrapLowerArgument 69 8 16 100000 25000000 ∈ Set.Icc (9 / 100 : ℝ) 1 ∧
    kadiriBootstrapLowerArgument 8 (13 / 2) 16 100000 25000000 ∈ Set.Icc (69 / 100 : ℝ) 1 ∧
    kadiriBootstrapLowerArgument (13 / 2) 6 16 100000 25000000 ∈ Set.Icc (79 / 100 : ℝ) 1 :=
  kadiriSix_three_argument_intervals le_rfl

end

end PrimeFactorUnimodality.Tests
