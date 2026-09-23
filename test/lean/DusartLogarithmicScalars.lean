import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicScalars

/-! # Regression statements for the decreasing logarithmic error -/

namespace PrimeFactorUnimodality.Tests

open Real

example {b : ℝ} (hb : 0 < b) :
    exp (-b / 2) ≤ 384 / b ^ 4 :=
  dusartLog_half_exp_le hb

example {b : ℝ} (hb : 50 ≤ b) :
    77 * exp (-b / 2) ≤ (6 / 25 : ℝ) / b :=
  dusartLog_low_le hb

example {b s : ℝ} (hb : 50 ≤ b) (hs : s ≤ 1 / (20 * b)) :
    1 + 3 * s ≤ (11 / 10 : ℝ) :=
  dusartLog_width_le hb hs

example {b s : ℝ} (hb : 50 ≤ b)
    (hs₀ : 1 / (60 * b) ≤ s) (hs₁ : s ≤ 1 / (20 * b)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ 8 * (11 / 10 : ℝ) ^ 4 * (60 * b) ^ 3 :=
  dusartLog_coefficient_le hb hs₀ hs₁

example {b : ℝ} (hb : 0 < b) :
    (8 * (11 / 10 : ℝ) ^ 4 * (60 * b) ^ 3) *
      (576 / (b / 56) ^ 4) * (4 / 10 ^ 18) ≤ (3 / 50 : ℝ) / b :=
  dusartLog_high_le hb

example {x : ℝ} (hx : 2 ≤ x) :
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x ≤ 4 / x :=
  dusartLog_correction_le hx

example {b : ℝ} (hb : 50 ≤ b) :
    4 / exp b ≤ (4 / 25 : ℝ) / b :=
  dusartLog_four_div_exp_le hb

end PrimeFactorUnimodality.Tests
