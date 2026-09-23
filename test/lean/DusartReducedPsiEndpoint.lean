import PrimeFactorUnimodality.Helpers.Analytic.DusartReducedPsiEndpoint

/-! # Reduced-cutoff interfaces and real-endpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real Set MeasureTheory

example {s : ℝ} (hs : s ≤ (1 / 599995 : ℝ)) :
    1 + 5 * s ≤ (1000009 / 1000000 : ℝ) := by
  exact PrimeFactorUnimodality.dusartReducedEndpoint_width_le hs

example {s : ℝ} (hs₀ : (1 / 600000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 599995 : ℝ)) :
    32 * (1 + 5 * s) ^ 6 / s ^ 5 ≤ (249 * 10 ^ 28 : ℝ) := by
  exact PrimeFactorUnimodality.dusartReducedEndpoint_high_coefficient_le hs₀ hs₁

example {s x : ℝ} (hs₀ : (1 / 600000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 599995 : ℝ)) (hx : (1440000000000 : ℝ) ≤ x) :
    dusartBoxPowerRelativeBudget 2 s x 25 1250000 25000000 (1 / 2) ≤
      dusartReducedEndpointAverageCap := by
  exact PrimeFactorUnimodality.dusartBoxPowerRelativeBudget_reduced_endpoint_le hs₀ hs₁ hx

example {x₀ : ℝ} (hx₀ : (1441000000000 : ℝ) ≤ x₀) :
    dusartBoxPowerPsiBound 2 (1 / 600000) x₀ 25 1250000 25000000 (1 / 2) <
      (1 / 36260 : ℝ) := by
  exact PrimeFactorUnimodality.dusartBoxPowerPsiBound_reduced_endpoint_lt hx₀

example {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x < (1 / 36260 : ℝ) := by
  exact PrimeFactorUnimodality.abs_psi_sub_div_lt_of_reduced_low_gap hx hgap

example {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    Chebyshev.theta x < x * (1 + 1 / 36260) := by
  exact PrimeFactorUnimodality.theta_lt_dusart_upper_of_reduced_low_gap hx hgap

example : dusartBoxPowerPsiBound 2 (1 / 600000) 1441000000000 25 1250000 25000000 (1 / 2) <
    (1 / 36260 : ℝ) := dusartBoxPowerPsiBound_reduced_endpoint_lt le_rfl

example : dusartReducedEndpointAverageCap + 5 * (1 / 600000 : ℝ) / 2 < 1 / 36260 := by
  norm_num [dusartReducedEndpointAverageCap]

example : 32 * (1 + 5 * (1 / 599995 : ℝ)) ^ 6 / (1 / 599995 : ℝ) ^ 5 ≤
    (249 * 10 ^ 28 : ℝ) :=
  dusartReducedEndpoint_high_coefficient_le (by norm_num) le_rfl

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi 1441000000000 - 1441000000000| / 1441000000000 < (1 / 36260 : ℝ) :=
  abs_psi_sub_div_lt_of_reduced_low_gap le_rfl hgap

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi (1441000000000 + 1 / 2) - (1441000000000 + 1 / 2)| /
      (1441000000000 + 1 / 2) < (1 / 36260 : ℝ) :=
  abs_psi_sub_div_lt_of_reduced_low_gap (by norm_num) hgap

end

end PrimeFactorUnimodality.Tests
