import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiEndpoint

/-! # Regression checks for explicit endpoint estimates and their hypotheses -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example {x : ℝ} (hx : (1440000000000 : ℝ) ≤ x) :
    exp (-(1 / 2) * Real.log x) ≤ (1 / 1200000 : ℝ) :=
  dusartEndpoint_half_log_decay_le hx

example {x : ℝ} (hx : (1440000000000 : ℝ) ≤ x) :
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x ≤ (4 / 1440000000000 : ℝ) :=
  dusartEndpoint_correction_le hx

example {s : ℝ} (hs : s ≤ (1 / 449997 : ℝ)) :
    1 + 3 * s ≤ (1000007 / 1000000 : ℝ) :=
  dusartEndpoint_width_le hs

example {s : ℝ} (hs₀ : (1 / 450000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 449997 : ℝ)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ (7291 * 10 ^ 14 : ℝ) :=
  dusartEndpoint_high_coefficient_le hs₀ hs₁

example {s x : ℝ} (hs₀ : (1 / 450000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 449997 : ℝ)) (hx : (1440000000000 : ℝ) ≤ x) :
    dusartBoxPowerRelativeBudget 0 s x 10 1000000 1000000000 (1 / 2) ≤
      dusartEndpointAverageCap :=
  dusartBoxPowerRelativeBudget_endpoint_le hs₀ hs₁ hx

example {x₀ : ℝ} (hx₀ : (1441000000000 : ℝ) ≤ x₀) :
    dusartBoxPowerPsiBound 0 (1 / 450000) x₀ 10 1000000 1000000000 (1 / 2) <
      (1 / 36260 : ℝ) :=
  dusartBoxPowerPsiBound_endpoint_lt hx₀

example {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x < (1 / 36260 : ℝ) :=
  abs_psi_sub_div_lt_of_billion_low_gap hx hgap

example {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    Chebyshev.theta x < x * (1 + 1 / 36260) :=
  theta_lt_dusart_upper_of_billion_low_gap hx hgap

example : exp (-(1 / 2) * Real.log (1440000000000 : ℝ)) ≤ (1 / 1200000 : ℝ) :=
  dusartEndpoint_half_log_decay_le le_rfl

example : 8 * (1 + 3 * (1 / 450000 : ℝ)) ^ 4 / (1 / 450000 : ℝ) ^ 3 ≤ 7291 * 10 ^ 14 :=
  dusartEndpoint_high_coefficient_le le_rfl (by norm_num)

example : 8 * (1 + 3 * (1 / 449997 : ℝ)) ^ 4 / (1 / 449997 : ℝ) ^ 3 ≤ 7291 * 10 ^ 14 :=
  dusartEndpoint_high_coefficient_le (by norm_num) le_rfl

example : dusartBoxPowerPsiBound 0 (1 / 450000) 1441000000000 10 1000000 1000000000 (1 / 2) <
    (1 / 36260 : ℝ) := dusartBoxPowerPsiBound_endpoint_lt le_rfl

example (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    Chebyshev.theta 1441000000000 < (1441000000000 : ℝ) * (1 + 1 / 36260) :=
  theta_lt_dusart_upper_of_billion_low_gap le_rfl hgap

end PrimeFactorUnimodality.Tests
