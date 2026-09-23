import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserSharpBudget

/-! # Regression tests for sharp Rosser tail estimates -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {h x R ν : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤
      1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ)))
    (hT : 10 < exp (ν * sqrt (Real.log x / R)))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex,
      exp (ν * sqrt (Real.log x / R)) ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m h x (exp (ν * sqrt (Real.log x / R)))‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserSharpTailBound (sqrt (Real.log x / R)) (m + 3 : ℕ) ν :=
  norm_dusartBoxXiHighSum_le_rosserSharp m hh hx hR hν hmargin hparam hT hreg

example (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤
      1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log x / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserSharpErrorBudget m h x R ν a H δ :=
  abs_dusartPsiAverageError_le_rosserSharpBudget m hh hx hR hν hν1 hmargin hparam
    ha haH hH hδ hHT hgap hreg

example (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / (m + 3 : ℕ) +
      sqrt ((Real.log (x - (m + 3 : ℕ) * h) / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log (x - (m + 3 : ℕ) * h) / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserSharpErrorBudget m h (x - (m + 3 : ℕ) * h) R ν a H δ)
        (dusartBoxRosserSharpErrorBudget m h x R ν a H δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxRosserSharpBudget m hh hx hR hν hν1 hmargin hparam
    ha haH hH hδ hHT hgap hreg

end PrimeFactorUnimodality.Tests
