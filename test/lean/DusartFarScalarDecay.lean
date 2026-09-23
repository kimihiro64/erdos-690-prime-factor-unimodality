import PrimeFactorUnimodality.Helpers.Analytic.DusartFarScalarDecay

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {X : ℝ} (hX : 28 ≤ X) :
    exp (-(4 / 5 : ℝ) * X) ≤ (1 / 5000000000 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_exp_step_le <;> assumption

example {X : ℝ} (hX : 28 ≤ X) :
    exp (-(5 / 4 : ℝ) * X) ≤ (1 / 10 ^ 15 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_exp_window_le <;> assumption

example {X : ℝ} (hX : 28 ≤ X) :
    (1000000000 : ℝ) ≤ exp ((4 / 5 : ℝ) * X) := by
  apply PrimeFactorUnimodality.dusartFar_cutoff_ge_billion <;> assumption

example {X : ℝ} (hX : 28 ≤ X) :
    36 * X ^ 4 * ((3 / 2 : ℝ) * exp (-(4 / 5 : ℝ) * X)) ≤ (1 / 100 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_smoothing_moment_le <;> assumption

example {X : ℝ} (hX : 28 ≤ X) :
    36 * X ^ 4 * (2048 * X * exp (-(5 / 4 : ℝ) * X)) ≤ (1 / 500 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_high_moment_le <;> assumption

example {X : ℝ} (hX : 28 ≤ X) :
    36 * X ^ 4 * (32 * X * exp (-(5 / 4 : ℝ) * X)) ≤ (1 / 500 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_window_moment_le <;> assumption

example {b : ℝ} (hb : 4704 ≤ b) :
    b ^ 2 * (77 * exp (-b / 2)) ≤ (1 / 500 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_low_moment_le <;> assumption

example {b : ℝ} (hb : 4704 ≤ b) :
    b ^ 2 * (4 / exp b) ≤ (1 / 1000 : ℝ) := by
  apply PrimeFactorUnimodality.dusartFar_correction_moment_le <;> assumption

example : 36 * (28 : ℝ) ^ 4 * ((3 / 2 : ℝ) * exp (-(4 / 5 : ℝ) * 28)) ≤
    (1 / 100 : ℝ) := dusartFar_smoothing_moment_le le_rfl

example : (4704 : ℝ) ^ 2 * (77 * exp (-(4704 : ℝ) / 2)) ≤ (1 / 500 : ℝ) :=
  dusartFar_low_moment_le le_rfl

end PrimeFactorUnimodality.Tests
