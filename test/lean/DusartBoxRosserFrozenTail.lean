import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenTail

/-! # Regression tests for the uniform starting-point estimate -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) {h x x₀ R p T : ℝ}
    (hh : 0 < h) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserClosedTailBound (Real.log x₀ / R) (m + 4 : ℕ) p T :=
  norm_dusartBoxXiHighSum_le_frozen_closed m hh hx₀ hx hR hp hpq hT hpeak hreg

example (m : ℕ) {s x x₀ R p T : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m (s * x) x T‖ / x ≤
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        xiRosserClosedTailBound (Real.log x₀ / R) (m + 4 : ℕ) p T :=
  norm_dusartBoxXiHighSum_div_le_frozen_closed m hs hx₀ hx hR hp hpq hT hpeak hreg

end PrimeFactorUnimodality.Tests
