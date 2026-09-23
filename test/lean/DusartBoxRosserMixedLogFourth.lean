import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserMixedLogFourth

/-! # Regression tests for complete Rosser cutoff selection -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {x R ν a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartLogFourthMixedBoxBound m x R ν a H δ + 1 / (8 * Real.log x ^ 4) :=
  abs_psi_sub_div_le_logFourthMixedBox m hx hR hν hν1 hmargin ha haH hH hδ hgap hreg

example (m : ℕ) {x R ν a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hbound : dusartLogFourthMixedBoxBound m x R ν a H δ ≤ 3 / (8 * Real.log x ^ 4)) :
    |ψ x - x| ≤ (1 / 2) * x / Real.log x ^ 4 :=
  abs_psi_sub_le_half_logFourth_of_mixed m hx hR hν hν1 hmargin ha haH hH hδ hgap hreg hbound

example {X R a H δ : ℝ}
    (hX : 3 ≤ X) (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hscalar : ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (ν : ℝ),
      0 < ν ∧ ν ≤ 1 ∧ 1 < (m + 3 : ℕ) * ν ^ 2 ∧
        dusartLogFourthMixedBoxBound m x R ν a H δ ≤ 3 / (8 * Real.log x ^ 4)) :
    HasPsiLogFourthError (1 / 2) X :=
  hasPsiLogFourthError_of_rosserMixed hX hR ha haH hH hδ hgap hreg hscalar

example {R a H δ : ℝ}
    (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hscalar : ∀ x : ℝ, (4e18 : ℝ) ≤ x → ∃ (m : ℕ) (ν : ℝ),
      0 < ν ∧ ν ≤ 1 ∧ 1 < (m + 3 : ℕ) * ν ^ 2 ∧
        dusartLogFourthMixedBoxBound m x R ν a H δ ≤ 3 / (8 * Real.log x ^ 4)) :
    HasThetaLogFourthError (648 / 1000) (4e18) :=
  hasThetaLogFourthError_648_of_rosserMixed hR ha haH hH hδ hgap hreg hscalar

end PrimeFactorUnimodality.Tests
