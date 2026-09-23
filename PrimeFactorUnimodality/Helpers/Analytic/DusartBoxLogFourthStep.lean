import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserRelative

/-! # An explicit admissible log-fourth smoothing step

For every box order, the relative step `1/(4*(m+3)*log(x)^4)` spends
exactly `1/(8*log(x)^4)` on smoothing. The lower adjacent base point is
independent of the order and stays above one for `x>=3`. Substitution in
the actual normalized psi estimate leaves an elementary two-average
budget, with `3/8` available for the target psi coefficient `1/2`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- A relative step reserving one quarter of the target log-fourth coefficient for smoothing. -/
def dusartLogFourthRelativeStep (m : ℕ) (x : ℝ) : ℝ :=
  1 / (4 * (m + 3 : ℕ) * Real.log x ^ 4)

/-- The lower adjacent base point for the chosen step, independent of the box order. -/
def dusartLogFourthLeft (x : ℝ) : ℝ := x * (1 - 1 / (4 * Real.log x ^ 4))

/-- The chosen step is strictly positive beyond one. -/
theorem dusartLogFourthRelativeStep_pos (m : ℕ) {x : ℝ} (hx : 1 < x) :
    0 < dusartLogFourthRelativeStep m x := by
  have hl := Real.log_pos hx
  unfold dusartLogFourthRelativeStep
  positivity

/-- The total relative smoothing width does not depend on the order. -/
theorem dusartLogFourthRelativeStep_width (m : ℕ) {x : ℝ} (hx : 1 < x) :
    (m + 3 : ℕ) * dusartLogFourthRelativeStep m x = 1 / (4 * Real.log x ^ 4) := by
  have hl := Real.log_pos hx
  have hn : (0 : ℝ) < (m + 3 : ℕ) := by positivity
  unfold dusartLogFourthRelativeStep
  field_simp

/-- The smoothing error consumes exactly one eighth of the log-fourth scale. -/
theorem dusartLogFourthRelativeStep_loss (m : ℕ) {x : ℝ} (hx : 1 < x) :
    (m + 3 : ℕ) * dusartLogFourthRelativeStep m x / 2 = 1 / (8 * Real.log x ^ 4) := by
  rw [dusartLogFourthRelativeStep_width m hx, div_div]
  congr 1
  ring

/-- The lower average retains at least three quarters of the base point. -/
theorem dusartLogFourthLeft_ge {x : ℝ} (hx : 3 ≤ x) : 3 * x / 4 ≤ dusartLogFourthLeft x := by
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr
    (Real.exp_one_lt_three.le.trans hx)
  have hpow : 1 ≤ Real.log x ^ 4 := one_le_pow₀ hl
  have hw : 1 / (4 * Real.log x ^ 4) ≤ (1 : ℝ) / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hpow])
  have hm := mul_le_mul_of_nonneg_left hw hx0.le
  unfold dusartLogFourthLeft
  nlinarith only [hm]

/-- Both actual averages remain in their analytic domain. -/
theorem one_lt_dusartLogFourthLeft {x : ℝ} (hx : 3 ≤ x) : 1 < dusartLogFourthLeft x :=
  lt_of_lt_of_le (by linarith : 1 < 3 * x / 4) (dusartLogFourthLeft_ge hx)

/-- The normalized two-average contribution, excluding the exactly known smoothing cost. -/
def dusartLogFourthBoxBound (m : ℕ) (x R ν a H δ : ℝ) : ℝ :=
  let s := dusartLogFourthRelativeStep m x
  let t := 1 - 1 / (4 * Real.log x ^ 4)
  max (t * dusartBoxRosserRelativeBudget m (s / t) (dusartLogFourthLeft x) R ν a H δ)
    (dusartBoxRosserRelativeBudget m s x R ν a H δ)

/-- The actual normalized psi estimate has an explicit admissible step and exact smoothing cost. -/
theorem abs_psi_sub_div_le_logFourthBox (m : ℕ) {x R ν a H δ : ℝ}
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
    |ψ x - x| / x ≤ dusartLogFourthBoxBound m x R ν a H δ + 1 / (8 * Real.log x ^ 4) := by
  have hx1 : 1 < x := by linarith
  have hleft : x * (1 - (m + 3 : ℕ) * dusartLogFourthRelativeStep m x) =
      dusartLogFourthLeft x := by rw [dusartLogFourthRelativeStep_width m hx1]; rfl
  have hb := abs_psi_sub_div_le_dusartBoxRosserRelative m
    (dusartLogFourthRelativeStep_pos m hx1) (by linarith : 0 < x)
    (by rw [hleft]; exact one_lt_dusartLogFourthLeft hx) hR hν hν1 hmargin
    (by simpa only [hleft] using hparam) ha haH hH hδ
    (by simpa only [hleft] using hHT) hgap hreg
  rw [dusartLogFourthRelativeStep_loss m hx1, dusartLogFourthRelativeStep_width m hx1] at hb
  exact hb

/-- A `3/8` scalar bound closes the required `1/2` psi coefficient at the same point. -/
theorem abs_psi_sub_le_half_logFourth_of_box (m : ℕ) {x R ν a H δ : ℝ}
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
    |ψ x - x| ≤ (1 / 2) * x / Real.log x ^ 4 := by
  have hb := (abs_psi_sub_div_le_logFourthBox m hx hR hν hν1 hmargin hparam
    ha haH hH hδ hHT hgap hreg).trans (add_le_add hbound le_rfl)
  have hx0 : 0 < x := by linarith
  have he : 3 / (8 * Real.log x ^ 4) + 1 / (8 * Real.log x ^ 4) =
      ((1 / 2) * x / Real.log x ^ 4) / x := by
    field_simp
    ring
  rw [he] at hb
  exact (div_le_div_iff_of_pos_right hx0).mp hb

end

end PrimeFactorUnimodality
