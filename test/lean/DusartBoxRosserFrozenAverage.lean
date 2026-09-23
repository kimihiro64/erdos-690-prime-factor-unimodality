import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenAverage

/-! # Regression tests for the uniform starting-point estimate -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x ≤
      (1 / (2 * (x₀ ^ 2 - 1)) + Real.log (2 * π)) / x₀ :=
  dusartBox_relative_correction_le hx₀ hx

example (m : ℕ) {s x x₀ a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x)
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiLowHeightIndices H, iteratedBoxAverageComplex (s * x) (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x ≤
      ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x₀)) *
        xiLowReciprocalNormBound a H δ :=
  norm_dusartBox_low_div_le_frozen m hs hx₀ hx ha haH hδ hgap

example (m : ℕ) {s x x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserFixedRelativeBudget m s x₀ R p a H δ :=
  abs_dusartPsiAverageError_div_le_frozen m hs hx₀ hx hR hp hpq ha haH hδ hgap hpeak hreg

end PrimeFactorUnimodality.Tests
