import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxSplitAverage

/-! # Split-low estimates: full powers, cutoff boundaries and uniform actual psi -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) (s x R p a U H δ : ℝ) :
    dusartBoxRosserSplitRelativeBudget m s x R p a U H δ ≤
      dusartBoxRosserFixedRelativeBudget m s x R p a H δ :=
  dusartBoxRosserSplitRelativeBudget_le_fixed m s x R p a U H δ

example (m : ℕ) (s x R p a H δ : ℝ) :
    dusartBoxRosserSplitRelativeBudget m s x R p a H H δ =
      dusartBoxRosserFixedRelativeBudget m s x R p a H δ :=
  dusartBoxRosserSplitRelativeBudget_self m s x R p a H δ

example (m : ℕ) {s x x₀ R p a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserSplitRelativeBudget m s x₀ R p a U H δ :=
  abs_dusartPsiAverageError_div_le_split_frozen m hs hx₀ hx hR hp hpq ha haU hUH hδ hgap hpeak hreg

end PrimeFactorUnimodality.Tests
