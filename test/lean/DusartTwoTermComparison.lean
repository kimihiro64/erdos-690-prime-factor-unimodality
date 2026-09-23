import PrimeFactorUnimodality.Helpers.Analytic.DusartTwoTermComparison

/-! # Regression statements for the direct log-square Dusart route -/

namespace PrimeFactorUnimodality.Tests

example {x : ℝ} (hx : 1 < x) :
    HasDerivAt dusartPiLower (1 / Real.log x - 2 / Real.log x ^ 3) x :=
  hasDerivAt_dusartPiLower hx

example {x : ℝ} (hx : 1 < x) :
    HasDerivAt dusartPiUpper
      (1 / Real.log x + (1381 / 5000 : ℝ) / Real.log x ^ 2 -
        (6381 / 2500 : ℝ) / Real.log x ^ 3) x :=
  hasDerivAt_dusartPiUpper hx

example {η x₀ : ℝ} (h₀ : 1 < x₀) :
    dusartPiLower x₀ ≤ dusartJ 2 (-η) x₀ x₀ ↔
      Chebyshev.theta x₀ * Real.log x₀ ^ 2 + x₀ * Real.log x₀ + η * x₀ ≤
        (Nat.primeCounting ⌊x₀⌋₊ : ℝ) * Real.log x₀ ^ 3 :=
  dusartPiLower_le_dusartJ_two_anchor_iff h₀

example {η x₀ : ℝ} (h₀ : 1 < x₀) :
    dusartJ 2 η x₀ x₀ ≤ dusartPiUpper x₀ ↔
      (Nat.primeCounting ⌊x₀⌋₊ : ℝ) * Real.log x₀ ^ 3 ≤
        Chebyshev.theta x₀ * Real.log x₀ ^ 2 +
          (6381 / 5000 : ℝ) * x₀ * Real.log x₀ - η * x₀ :=
  dusartJ_two_le_dusartPiUpper_anchor_iff h₀

example {η x₀ x : ℝ}
    (h₀ : 1 < x₀) (hx : x₀ ≤ x) (hη : 0 ≤ η) (hη2 : η ≤ 2)
    (hanchor : dusartPiLower x₀ ≤ dusartJ 2 (-η) x₀ x₀) :
    dusartPiLower x ≤ dusartJ 2 (-η) x₀ x :=
  dusartPiLower_le_dusartJ_two h₀ hx hη hη2 hanchor

example {η x₀ x : ℝ}
    (h₀ : 1 < x₀) (hx : x₀ ≤ x) (hη : 0 ≤ η)
    (hmargin : (6381 / 2500 : ℝ) + η ≤ (1381 / 5000 : ℝ) * Real.log x₀)
    (hanchor : dusartJ 2 η x₀ x₀ ≤ dusartPiUpper x₀) :
    dusartJ 2 η x₀ x ≤ dusartPiUpper x :=
  dusartJ_two_le_dusartPiUpper h₀ hx hη hmargin hanchor

end PrimeFactorUnimodality.Tests
