import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxSplitPointwise

/-! # Split-low estimates: full powers, cutoff boundaries and uniform actual psi -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) {s x₀ R p a U H δ : ℝ}
    (hs : (m + 3 : ℕ) * s ≤ 1) :
    dusartRosserSplitPsiBound m s x₀ R p a U H δ ≤
      dusartRosserFrozenPsiBound m s x₀ R p a H δ :=
  dusartRosserSplitPsiBound_le_frozen m hs

example (m : ℕ) (s x₀ R p a H δ : ℝ) :
    dusartRosserSplitPsiBound m s x₀ R p a H H δ =
      dusartRosserFrozenPsiBound m s x₀ R p a H δ :=
  dusartRosserSplitPsiBound_self m s x₀ R p a H δ

example (m : ℕ) {s x x₀ R p a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartRosserSplitPsiBound m s x₀ R p a U H δ :=
  abs_psi_sub_div_le_split_frozen m hs hx₀ hx hl₀ hR hp hpq ha haU hUH hδ hgap hpeak hreg

example (m : ℕ) {s x₀ R p a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x₀ - x₀| / x₀ ≤ dusartRosserSplitPsiBound m s x₀ R p a U H δ :=
  abs_psi_sub_div_le_split_frozen m hs hx₀ le_rfl hl₀ hR hp hpq ha haU hUH hδ hgap hpeak hreg

example {s x x₀ R p a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (4 : ℕ))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartRosserSplitPsiBound 0 s x₀ R p a U H δ :=
  abs_psi_sub_div_le_split_frozen 0 hs hx₀ hx hl₀ hR hp hpq ha haU hUH hδ hgap hpeak hreg

end PrimeFactorUnimodality.Tests
