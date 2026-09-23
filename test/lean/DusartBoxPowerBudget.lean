import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerBudget

/-! # Regression checks for explicit endpoint estimates and their hypotheses -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) {s x x₀ a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x)
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPowerRelativeBudget m s x₀ a U H δ :=
  abs_dusartPsiAverageError_div_le_power_frozen m hs hx₀ hx ha haU hUH hδ hgap

example (m : ℕ) {s x x₀ a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    |ψ x - x| / x ≤ dusartBoxPowerPsiBound m s x₀ a U H δ :=
  abs_psi_sub_div_le_power_frozen m hs hx₀ hx hl₀ ha haU hUH hδ hgap

example {s x x₀ a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (3 : ℕ) * s))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    |ψ x - x| / x ≤ dusartBoxPowerPsiBound 0 s x₀ a U H δ :=
  abs_psi_sub_div_le_power_frozen 0 hs hx₀ hx hl₀ ha haU hUH hδ hgap

end PrimeFactorUnimodality.Tests
