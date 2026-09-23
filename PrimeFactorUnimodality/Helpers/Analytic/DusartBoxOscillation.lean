import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxZeroSplit
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageScaling

/-! # The actual low xi sum as a fixed weighted phase sum

Relative smoothing makes the coefficients independent of the evaluation point.
The logarithmic center is arbitrary, so the shared evaluator only needs a
small residual parameter. The finite set retains both signs and all divisor
labels; no zero separation or simplicity is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

/-- Fixed coefficient, with the logarithmic center phase absorbed once. -/
def dusartBoxZeroCoefficient (m : ℕ) (s u : ℝ) (z : RiemannXiDivisorZeroIndex) : ℂ :=
  iteratedBoxAverageComplex s (m + 3)
    (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) 1 *
      exp (I * ((u * (riemannXiDivisorZeroValue z).im : ℝ) : ℂ))

/-- The finite phase sum keeps cancellation among the actual low zeros. -/
def dusartBoxLowPhaseSum (m : ℕ) (s u T v : ℝ) : ℂ :=
  ∑ z ∈ xiLowHeightIndices T, dusartBoxZeroCoefficient m s u z *
    exp (I * ((v * (riemannXiDivisorZeroValue z).im : ℝ) : ℂ))

/-- The critical-line low sum is exactly its phase sum times the square-root amplitude. -/
theorem dusartBox_low_eq_phase (m : ℕ) {s x T : ℝ} (u : ℝ)
    (hs : 0 < s) (hx : 0 < x)
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2) :
    (∑ z ∈ xiLowHeightIndices T, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x) =
      (Real.exp (Real.log x / 2) : ℂ) * dusartBoxLowPhaseSum m s u T (Real.log x - u) := by
  unfold dusartBoxLowPhaseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hp : ∀ j : ℕ, riemannXiDivisorZeroValue z + j ≠ 0 := by
    intro j hj
    have hr := congrArg Complex.re hj
    simp only [add_re, natCast_re, zero_re, hline z hz] at hr
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  rw [iteratedBoxAverageComplex_cpow_div_phase hs hx hp (hline z hz)]
  rw [show (1 / 2 : ℝ) * Real.log x = Real.log x / 2 by ring]
  congr 1
  unfold dusartBoxZeroCoefficient
  rw [mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

/-- Normalizing the actual low sum gives the inverse-square-root factor exactly. -/
theorem norm_dusartBox_low_div_eq_phase (m : ℕ) {s x T : ℝ} (u : ℝ)
    (hs : 0 < s) (hx : 0 < x)
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2) :
    ‖∑ z ∈ xiLowHeightIndices T, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x =
      Real.exp (-Real.log x / 2) * ‖dusartBoxLowPhaseSum m s u T (Real.log x - u)‖ := by
  rw [dusartBox_low_eq_phase m u hs hx hline, norm_mul, norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (Real.log x / 2) / x = Real.exp (-Real.log x / 2) := by
    apply (div_eq_iff hx.ne').mpr
    calc
      _ = Real.exp (-Real.log x / 2 + Real.log x) := by congr 1; ring
      _ = Real.exp (-Real.log x / 2) * x := by rw [Real.exp_add, Real.exp_log hx]
  calc
    _ = (Real.exp (Real.log x / 2) / x) *
        ‖dusartBoxLowPhaseSum m s u T (Real.log x - u)‖ := by ring
    _ = _ := by rw [he]

end

end PrimeFactorUnimodality
