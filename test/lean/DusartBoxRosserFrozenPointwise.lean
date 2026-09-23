import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenPointwise

/-! # Regression tests for the uniform starting-point estimate -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) {s x x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartRosserFrozenPsiBound m s x₀ R p a H δ :=
  abs_psi_sub_div_le_frozen m hs hx₀ hx hl₀ hR hp hpq ha haH hδ hgap hpeak hreg

example {s x x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (0 + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (0 + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (0 + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartRosserFrozenPsiBound 0 s x₀ R p a H δ :=
  abs_psi_sub_div_le_frozen 0 hs hx₀ hx hl₀ hR hp hpq ha haH hδ hgap hpeak hreg

-- The starting point itself is included in the ray.
example (m : ℕ) {s x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x₀ - x₀| / x₀ ≤ dusartRosserFrozenPsiBound m s x₀ R p a H δ :=
  abs_psi_sub_div_le_frozen m hs hx₀ le_rfl hl₀ hR hp hpq ha haH hδ hgap hpeak hreg

end PrimeFactorUnimodality.Tests
