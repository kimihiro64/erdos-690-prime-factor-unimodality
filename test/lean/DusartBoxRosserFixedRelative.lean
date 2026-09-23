import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFixedRelative

/-! # Regression tests for complete Rosser cutoff selection -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {s x R p a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) :
    dusartBoxRosserClosedErrorBudget m (s * x) x R p a H H δ =
      x * dusartBoxRosserFixedRelativeBudget m s x R p a H δ :=
  dusartBoxRosserClosedErrorBudget_fixed_scale m hs hx

example (m : ℕ) {s x R p a H δ : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserFixedRelativeBudget m s x R p a H δ :=
  abs_dusartPsiAverageError_div_le_rosserFixed m hs hx hR hp hpq ha haH hH hδ hgap hpeak hreg

example (m : ℕ) {s x R p a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 1 < x * (1 - (m + 3 : ℕ) * s))
    (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) * dusartBoxRosserFixedRelativeBudget m (s / (1 - (m + 3 : ℕ) * s))
        (x * (1 - (m + 3 : ℕ) * s)) R p a H δ)
        (dusartBoxRosserFixedRelativeBudget m s x R p a H δ) +
          (m + 3 : ℕ) * s / 2 :=
  abs_psi_sub_div_le_dusartBoxRosserFixed m hs hx hl hR hp hpq ha haH hH hδ hgap hpeak hreg

example (m : ℕ) {x R p a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartLogFourthFixedBoxBound m x R p a H δ + 1 / (8 * Real.log x ^ 4) :=
  abs_psi_sub_div_le_logFourthFixedBox m hx hR hp hpq ha haH hH hδ hgap hpeak hreg

end PrimeFactorUnimodality.Tests
