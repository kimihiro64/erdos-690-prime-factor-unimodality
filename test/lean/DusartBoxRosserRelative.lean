import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserRelative

/-! # Regression tests for normalized Rosser estimates -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) :
    dusartBoxRosserSharpErrorBudget m (s * x) x R ν a H δ =
      x * dusartBoxRosserRelativeBudget m s x R ν a H δ :=
  dusartBoxRosserSharpErrorBudget_scale m hs hx

example (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤
      1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log x / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserRelativeBudget m s x R ν a H δ :=
  abs_dusartPsiAverageError_div_le_rosserRelative m hs hx hR hν hν1 hmargin hparam ha haH hH hδ
    hHT hgap hreg

example (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 1 < x * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / (m + 3 : ℕ) +
      sqrt ((Real.log (x * (1 - (m + 3 : ℕ) * s)) / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log (x * (1 - (m + 3 : ℕ) * s)) / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxRosserRelativeBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) R ν a H δ)
        (dusartBoxRosserRelativeBudget m s x R ν a H δ) + (m + 3 : ℕ) * s / 2 :=
  abs_psi_sub_div_le_dusartBoxRosserRelative m hs hx hl hR hν hν1 hmargin hparam ha haH hH hδ hHT
    hgap hreg

end PrimeFactorUnimodality.Tests
