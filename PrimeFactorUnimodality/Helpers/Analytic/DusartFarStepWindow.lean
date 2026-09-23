import PrimeFactorUnimodality.Helpers.Analytic.DusartFarKernelBounds
import PrimeFactorUnimodality.Helpers.Analytic.DusartFarScalarDecay

/-! # A stable exponential smoothing window for both adjacent averages

Allow a factor-two variation in the relative step about exp(-4X/5).
The high-tail exponent cancels its cubic reciprocal step cost exactly.
The width and finite window are bounded independently of this variation.
-/

namespace PrimeFactorUnimodality

open Real

/-- The relative step window keeps the total order-three smoothing width small. -/
theorem dusartFar_width_le {X s : ℝ} (hX : 28 ≤ X)
    (hs : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) : 1 + 3 * s ≤ (11 / 10 : ℝ) := by
  have he := dusartFar_exp_step_le hX
  linarith

/-- The finite-window scalar after multiplication by the smoothing width. -/
theorem dusartFar_window_le {X s : ℝ} (hX : 28 ≤ X) (hs : 0 < s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) :
    (1 + 3 * s) * (2 * xiRosserNuWindowBound X (4 / 5)) ≤
      32 * X * exp (-(5 / 4 : ℝ) * X) := by
  have hw := dusartFar_width_le hX hs₁
  have hXpos : 0 < X := by linarith
  calc
    _ ≤ (1 + 3 * s) * (16 * X * exp (-(5 / 4 : ℝ) * X)) :=
      mul_le_mul_of_nonneg_left (xiRosserNuWindowBound_four_fifths_le hX) (by positivity)
    _ ≤ 2 * (16 * X * exp (-(5 / 4 : ℝ) * X)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- The cubic smoothing coefficient is bounded uniformly throughout the step window. -/
theorem dusartFar_high_coefficient_le {X s : ℝ} (hX : 28 ≤ X)
    (hs₀ : exp (-(4 / 5 : ℝ) * X) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ 128 / exp (-(4 / 5 : ℝ) * X) ^ 3 := by
  have hs : 0 < s := (by positivity : 0 < exp (-(4 / 5 : ℝ) * X) / 2).trans_le hs₀
  have hw := dusartFar_width_le hX hs₁
  have hn : (1 + 3 * s) ^ 4 ≤ 2 :=
    (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 3 * s) hw 4).trans (by norm_num)
  have hd := pow_le_pow_left₀ (by positivity : 0 ≤ exp (-(4 / 5 : ℝ) * X) / 2) hs₀ 3
  calc
    _ ≤ 16 / s ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 16 / (exp (-(4 / 5 : ℝ) * X) / 2) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
    _ = _ := by ring

/-- Exact exponential cancellation leaves the same damping as the finite window. -/
theorem dusartFar_high_le {X s : ℝ} (hX : 28 ≤ X)
    (hs₀ : exp (-(4 / 5 : ℝ) * X) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * X)) :
    (8 * (1 + 3 * s) ^ 4 / s ^ 3) * xiRosserSharpTailBound X 3 (4 / 5) ≤
      2048 * X * exp (-(5 / 4 : ℝ) * X) := by
  have hs : 0 < s := (by positivity : 0 < exp (-(4 / 5 : ℝ) * X) / 2).trans_le hs₀
  have hXpos : 0 < X := by linarith
  have heq : exp (-(4 / 5 : ℝ) * X) ^ 3 = exp (-(12 / 5 : ℝ) * X) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (8 * (1 + 3 * s) ^ 4 / s ^ 3) * (16 * X * exp (-(73 / 20 : ℝ) * X)) :=
      mul_le_mul_of_nonneg_left (xiRosserSharpTailBound_four_fifths_le hX) (by positivity)
    _ ≤ (128 / exp (-(4 / 5 : ℝ) * X) ^ 3) * (16 * X * exp (-(73 / 20 : ℝ) * X)) :=
      mul_le_mul_of_nonneg_right (dusartFar_high_coefficient_le hX hs₀ hs₁) (by positivity)
    _ = 2048 * X * (exp (-(73 / 20 : ℝ) * X) / exp (-(12 / 5 : ℝ) * X)) := by
      rw [heq]
      ring
    _ = _ := by
      rw [← Real.exp_sub]
      congr 2
      ring

end PrimeFactorUnimodality
