import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxLogFourthStep

/-! # Regression tests for normalized Rosser estimates -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {x : ℝ} (hx : 1 < x) :
    0 < dusartLogFourthRelativeStep m x :=
  dusartLogFourthRelativeStep_pos m hx

example (m : ℕ) {x : ℝ} (hx : 1 < x) :
    (m + 3 : ℕ) * dusartLogFourthRelativeStep m x = 1 / (4 * Real.log x ^ 4) :=
  dusartLogFourthRelativeStep_width m hx

example (m : ℕ) {x : ℝ} (hx : 1 < x) :
    (m + 3 : ℕ) * dusartLogFourthRelativeStep m x / 2 = 1 / (8 * Real.log x ^ 4) :=
  dusartLogFourthRelativeStep_loss m hx

example {x : ℝ} (hx : 3 ≤ x) : 3 * x / 4 ≤ dusartLogFourthLeft x :=
  dusartLogFourthLeft_ge hx

example {x : ℝ} (hx : 3 ≤ x) : 1 < dusartLogFourthLeft x :=
  one_lt_dusartLogFourthLeft hx

example (m : ℕ) {x R ν a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / (m + 3 : ℕ) +
      sqrt ((Real.log (dusartLogFourthLeft x) / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log (dusartLogFourthLeft x) / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartLogFourthBoxBound m x R ν a H δ + 1 / (8 * Real.log x ^ 4) :=
  abs_psi_sub_div_le_logFourthBox m hx hR hν hν1 hmargin hparam ha haH hH hδ hHT hgap hreg

example (m : ℕ) {x R ν a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / (m + 3 : ℕ) +
      sqrt ((Real.log (dusartLogFourthLeft x) / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log (dusartLogFourthLeft x) / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hbound : dusartLogFourthBoxBound m x R ν a H δ ≤ 3 / (8 * Real.log x ^ 4)) :
    |ψ x - x| ≤ (1 / 2) * x / Real.log x ^ 4 :=
  abs_psi_sub_le_half_logFourth_of_box m hx hR hν hν1 hmargin hparam ha haH hH hδ hHT hgap hreg
    hbound

example : dusartLogFourthRelativeStep 0 (exp 1) = 1 / 12 := by
  norm_num [dusartLogFourthRelativeStep, Real.log_exp]

example : dusartLogFourthRelativeStep 17 (exp 1) = 1 / 80 := by
  norm_num [dusartLogFourthRelativeStep, Real.log_exp]

-- All orders give exactly the same lower adjacent base point.
example (m n : ℕ) {x : ℝ} (hx : 1 < x) :
    x * (1 - (m + 3 : ℕ) * dusartLogFourthRelativeStep m x) =
      x * (1 - (n + 3 : ℕ) * dusartLogFourthRelativeStep n x) := by
  rw [dusartLogFourthRelativeStep_width m hx, dusartLogFourthRelativeStep_width n hx]

example : 1 < dusartLogFourthLeft 3 := one_lt_dusartLogFourthLeft le_rfl

end PrimeFactorUnimodality.Tests
