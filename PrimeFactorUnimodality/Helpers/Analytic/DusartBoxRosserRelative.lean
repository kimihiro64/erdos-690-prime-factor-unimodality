import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserSharpBudget

/-! # Dimensionless Rosser bounds for the actual psi error

Writing the box step as `s*x` cancels all large algebraic powers of `x`
from the normalized high-tail coefficient. Adjacent averages have relative
steps `s` and `s/(1-(m+3)*s)`. The identities are exact, so a scalar check
of this smaller expression certifies the existing actual pointwise bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The sharp error budget divided by the base point, with all power cancellation performed. -/
def dusartBoxRosserRelativeBudget (m : ℕ) (s x R ν a H δ : ℝ) : ℝ :=
  let X := sqrt (Real.log x / R)
  ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ +
    (1 + (m + 3 : ℕ) * s) * (2 * xiRosserNuWindowBound X ν) +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      xiRosserSharpTailBound X (m + 3 : ℕ) ν +
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x

/-- Normalization cancels the large powers exactly, without a numerical approximation. -/
theorem dusartBoxRosserSharpErrorBudget_scale (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) :
    dusartBoxRosserSharpErrorBudget m (s * x) x R ν a H δ =
      x * dusartBoxRosserRelativeBudget m s x R ν a H δ := by
  have hU : x + (m + 3 : ℕ) * (s * x) = x * (1 + (m + 3 : ℕ) * s) := by ring
  have hC : 2 ^ (m + 3) * (x * (1 + (m + 3 : ℕ) * s)) ^ (m + 4) /
      (s * x) ^ (m + 3) =
      x * (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) := by
    rw [mul_pow, mul_pow, show m + 4 = (m + 3) + 1 by omega, pow_succ x]
    field_simp
  have hE : x * ((1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x) =
      1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π) := by
    calc
      _ = (x / x) * (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) := by ring
      _ = _ := by rw [div_self hx.ne', one_mul]
  unfold dusartBoxRosserSharpErrorBudget dusartBoxRosserRelativeBudget
  rw [hU, hC]
  linear_combination -hE

/-- The actual average satisfies the dimensionless budget with no large power of the base point. -/
theorem abs_dusartPsiAverageError_div_le_rosserRelative (m : ℕ) {s x R ν a H δ : ℝ}
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
      dusartBoxRosserRelativeBudget m s x R ν a H δ := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have h := abs_dusartPsiAverageError_le_rosserSharpBudget m (mul_pos hs hx0) hx hR hν hν1
    hmargin hparam ha haH hH hδ hHT hgap hreg
  rw [dusartBoxRosserSharpErrorBudget_scale m hs hx0] at h
  exact (div_le_iff₀ hx0).mpr (by simpa only [mul_comm] using h)

/-- Adjacent averages use an exact rescaling of the lower relative step. -/
theorem abs_psi_sub_div_le_dusartBoxRosserRelative (m : ℕ) {s x R ν a H δ : ℝ}
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
        (dusartBoxRosserRelativeBudget m s x R ν a H δ) + (m + 3 : ℕ) * s / 2 := by
  have hy : x - (m + 3 : ℕ) * (s * x) = x * (1 - (m + 3 : ℕ) * s) := by ring
  have hleft : 1 < x - (m + 3 : ℕ) * (s * x) := by rwa [hy]
  have hy0 : 0 < x * (1 - (m + 3 : ℕ) * s) := lt_trans zero_lt_one hl
  have ht : 0 < 1 - (m + 3 : ℕ) * s := (mul_pos_iff_of_pos_left hx).mp hy0
  have hstep : (s / (1 - (m + 3 : ℕ) * s)) * (x * (1 - (m + 3 : ℕ) * s)) = s * x := by
    calc
      _ = (s * x) * ((1 - (m + 3 : ℕ) * s) / (1 - (m + 3 : ℕ) * s)) := by ring
      _ = _ := by rw [div_self ht.ne', mul_one]
  have hlow := dusartBoxRosserSharpErrorBudget_scale (R := R) (ν := ν) (a := a) (H := H)
    (δ := δ) m (div_pos hs ht) hy0
  rw [hstep] at hlow
  have h := abs_psi_sub_le_dusartBoxRosserSharpBudget m (mul_pos hs hx) hleft hR hν hν1
    hmargin (by simpa only [hy] using hparam) ha haH hH hδ
    (by simpa only [hy] using hHT) hgap hreg
  rw [hy, hlow, dusartBoxRosserSharpErrorBudget_scale m hs hx, mul_assoc,
    ← mul_max_of_nonneg _ _ hx.le] at h
  apply (div_le_iff₀ hx).mpr
  convert h using 1
  ring

end

end PrimeFactorUnimodality
