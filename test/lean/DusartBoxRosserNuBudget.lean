import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserNuBudget

/-! # The actual psi consumer with exponent and cutoff choices discharged -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2) (hH : 20 ≤ H)
    (hHT : H ≤ exp (ν * sqrt (Real.log x / R))) :
    dusartBoxRosserBandErrorBudget m h x R ((m + 4 : ℕ) - 1 / ν ^ 2) a H
        (exp (ν * sqrt (Real.log x / R))) δ ≤ dusartBoxRosserNuErrorBudget m h x R ν a H δ :=
  dusartBoxRosserBandErrorBudget_le_nu m hh hx hR hν hmargin hH hHT

example {h x R a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hH : 20 ≤ H)
    (hHT : H ≤ exp (sqrt (Real.log x / R))) :
    dusartBoxRosserBandErrorBudget 0 h x R 3 a H (exp (sqrt (Real.log x / R))) δ ≤
      dusartBoxRosserNuErrorBudget 0 h x R 1 a H δ := by
  have h := dusartBoxRosserBandErrorBudget_le_nu (ν := 1) (a := a) (δ := δ) 0 hh hx hR
    (by norm_num) (by norm_num) hH (by simpa using hHT)
  norm_num at h
  exact h

example (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log x / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserNuErrorBudget m h x R ν a H δ :=
  abs_dusartPsiAverageError_le_rosserNuBudget m hh hx hR hν hν1 hmargin
    ha haH hH hδ hHT hgap hreg

-- No separately supplied exponent, turning condition, or common cutoff is required.
example (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log (x - (m + 3 : ℕ) * h) / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserNuErrorBudget m h (x - (m + 3 : ℕ) * h) R ν a H δ)
        (dusartBoxRosserNuErrorBudget m h x R ν a H δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxRosserNuBudget m hh hx hR hν hν1 hmargin
    ha haH hH hδ hHT hgap hreg

end PrimeFactorUnimodality.Tests
