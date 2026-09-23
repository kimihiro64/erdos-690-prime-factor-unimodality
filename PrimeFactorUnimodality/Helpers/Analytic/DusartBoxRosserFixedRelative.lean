import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxLogFourthStep
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserClosedBudget

/-! # Fixed-height Rosser estimates with exact normalization

Equal cutoffs remove the finite intermediate band. The resulting actual
average and pointwise estimates do not require a growing-cutoff domain
or the sharp density parameter condition. Their high-tail turning point
must lie below the fixed height; the power exponent stays adjustable.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The normalized fixed-height estimate with no intermediate band. -/
def dusartBoxRosserFixedRelativeBudget (m : ℕ) (s x R p a H δ : ℝ) : ℝ :=
  ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      xiRosserClosedTailBound (Real.log x / R) (m + 4 : ℕ) p H +
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x

/-- At equal cutoffs, the normalized fixed-height expression is exact. -/
theorem dusartBoxRosserClosedErrorBudget_fixed_scale (m : ℕ) {s x R p a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) :
    dusartBoxRosserClosedErrorBudget m (s * x) x R p a H H δ =
      x * dusartBoxRosserFixedRelativeBudget m s x R p a H δ := by
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
  simp only [dusartBoxRosserClosedErrorBudget, dusartBoxLowBandBudget,
    dusartBoxRosserClosedTailBudget, xiBandReciprocalNormBound_self, mul_zero, add_zero]
  unfold dusartBoxRosserFixedRelativeBudget
  rw [hU, hC]
  linear_combination -hE

/-- The actual average satisfies the fixed-height relative bound. -/
theorem abs_dusartPsiAverageError_div_le_rosserFixed (m : ℕ) {s x R p a H δ : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserFixedRelativeBudget m s x R p a H δ := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have he := abs_dusartPsiAverageError_le_rosserClosedBudget m (mul_pos hs hx0) hx hR hp hpq
    ha haH hH le_rfl hδ hgap hpeak hreg
  rw [dusartBoxRosserClosedErrorBudget_fixed_scale m hs hx0] at he
  exact (div_le_iff₀ hx0).mpr (by simpa only [mul_comm] using he)

/-- Adjacent actual averages give the fixed-height pointwise estimate. -/
theorem abs_psi_sub_div_le_dusartBoxRosserFixed (m : ℕ) {s x R p a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 1 < x * (1 - (m + 3 : ℕ) * s))
    (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) * dusartBoxRosserFixedRelativeBudget m (s / (1 - (m + 3 : ℕ) * s))
        (x * (1 - (m + 3 : ℕ) * s)) R p a H δ)
        (dusartBoxRosserFixedRelativeBudget m s x R p a H δ) +
          (m + 3 : ℕ) * s / 2 := by
  have hy : x - (m + 3 : ℕ) * (s * x) = x * (1 - (m + 3 : ℕ) * s) := by ring
  have hleft : 1 < x - (m + 3 : ℕ) * (s * x) := by rwa [hy]
  have hy0 : 0 < x * (1 - (m + 3 : ℕ) * s) := lt_trans zero_lt_one hl
  have ht : 0 < 1 - (m + 3 : ℕ) * s := (mul_pos_iff_of_pos_left hx).mp hy0
  have hstep : (s / (1 - (m + 3 : ℕ) * s)) * (x * (1 - (m + 3 : ℕ) * s)) = s * x := by
    calc
      _ = (s * x) * ((1 - (m + 3 : ℕ) * s) / (1 - (m + 3 : ℕ) * s)) := by ring
      _ = _ := by rw [div_self ht.ne', mul_one]
  have hlow := dusartBoxRosserClosedErrorBudget_fixed_scale
    (R := R) (p := p) (a := a) (H := H) (δ := δ) m (div_pos hs ht) hy0
  rw [hstep] at hlow
  have he := abs_psi_sub_le_dusartBoxRosserClosedBudget m (mul_pos hs hx) hleft hR hp hpq
    ha haH hH le_rfl hδ hgap hpeak hreg
  rw [hy, hlow, dusartBoxRosserClosedErrorBudget_fixed_scale m hs hx,
    mul_assoc, ← mul_max_of_nonneg _ _ hx.le] at he
  apply (div_le_iff₀ hx).mpr
  convert he using 1
  ring

/-- The fixed-height two-average contribution with the explicit log-fourth step. -/
def dusartLogFourthFixedBoxBound (m : ℕ) (x R p a H δ : ℝ) : ℝ :=
  let s := dusartLogFourthRelativeStep m x
  let t := 1 - 1 / (4 * Real.log x ^ 4)
  max (t * dusartBoxRosserFixedRelativeBudget m (s / t) (dusartLogFourthLeft x) R p a H δ)
    (dusartBoxRosserFixedRelativeBudget m s x R p a H δ)

/-- The chosen step retains the fixed-height bound and exact smoothing allowance. -/
theorem abs_psi_sub_div_le_logFourthFixedBox (m : ℕ) {x R p a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartLogFourthFixedBoxBound m x R p a H δ + 1 / (8 * Real.log x ^ 4) := by
  have hx1 : 1 < x := by linarith
  have hleft : x * (1 - (m + 3 : ℕ) * dusartLogFourthRelativeStep m x) =
      dusartLogFourthLeft x := by rw [dusartLogFourthRelativeStep_width m hx1]; rfl
  have hb := abs_psi_sub_div_le_dusartBoxRosserFixed m (dusartLogFourthRelativeStep_pos m hx1)
    (by linarith : 0 < x) (by rw [hleft]; exact one_lt_dusartLogFourthLeft hx)
    hR hp hpq ha haH hH hδ hgap hpeak hreg
  rw [dusartLogFourthRelativeStep_loss m hx1, dusartLogFourthRelativeStep_width m hx1] at hb
  exact hb

end

end PrimeFactorUnimodality
