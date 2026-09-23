import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiEulerEvaluation

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example {N : ℕ} (hN : 0 < N)
    (m : ℕ) (t : ℝ) :
    |xiNormalizedValue t - xiEulerApprox N m t| ≤ xiEulerError N m t := by
  exact PrimeFactorUnimodality.abs_xiNormalizedValue_sub_eulerApprox_le hN m t

example {N : ℕ} (hN : 0 < N)
    (m : ℕ) {t θ ε δ : ℝ} {w : ℂ}
    (hw : ‖zetaEulerApproxOrder N ((1 / 2 : ℂ) + t * I) m - w‖ ≤ ε)
    (hθ : |turingStirlingPhase t - θ| ≤ δ) :
    |xiNormalizedValue t - (exp (I * θ) * w).re| ≤
      zetaEulerError N ((1 / 2 : ℂ) + t * I) m + ε + ‖w‖ * (1 / 10 + δ) := by
  exact PrimeFactorUnimodality.abs_xiNormalizedValue_sub_roundedEuler_le hN m hw hθ

example {N m : ℕ} (hN : 0 < N) {t : ℝ}
    (hmargin : xiEulerError N m t < xiEulerApprox N m t) :
    0 < xiCriticalLineValue t := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_pos_of_eulerApprox hN hmargin

example {N m : ℕ} (hN : 0 < N) {t : ℝ}
    (hmargin : xiEulerApprox N m t < -xiEulerError N m t) :
    xiCriticalLineValue t < 0 := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_neg_of_eulerApprox hN hmargin

example {N M k m : ℕ}
    (hN : 0 < N) (hM : 0 < M) {a b : ℝ}
    (hmargin :
      (xiEulerError N k a < xiEulerApprox N k a ∧
        xiEulerApprox M m b < -xiEulerError M m b) ∨
      (xiEulerApprox N k a < -xiEulerError N k a ∧
        xiEulerError M m b < xiEulerApprox M m b)) :
    xiCriticalLineValue a * xiCriticalLineValue b < 0 := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_mul_neg_of_eulerApprox hN hM hmargin

example (t : ℝ) : |xiNormalizedValue t - xiEulerApprox 1 0 t| ≤ xiEulerError 1 0 t :=
  abs_xiNormalizedValue_sub_eulerApprox_le (by norm_num) 0 t

example {N : ℕ} (hN : 0 < N) (m : ℕ) :
    |xiNormalizedValue (-100) - xiEulerApprox N m (-100)| ≤ xiEulerError N m (-100) :=
  abs_xiNormalizedValue_sub_eulerApprox_le hN m (-100)

end

end PrimeFactorUnimodality.Tests
