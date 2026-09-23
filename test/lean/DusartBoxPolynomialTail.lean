import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPolynomialTail

/-! # Regression statements for the decreasing logarithmic error -/

namespace PrimeFactorUnimodality.Tests

open Real

example (m n : ℕ) {s x R T : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hR : 0 < R) (hT : 10 < T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m (s * x) x T‖ / x ≤
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        ((n.factorial : ℝ) ^ 2 / (Real.log x / R) ^ n) *
          xiRosserPowerTailBound (m + 3 : ℕ) T :=
  norm_dusartBoxXiHighSum_div_le_polynomial m n hs hx hR hT hreg

end PrimeFactorUnimodality.Tests
