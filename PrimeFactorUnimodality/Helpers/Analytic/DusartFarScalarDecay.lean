import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicScalars
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Exp.Monomial

/-! # Uniform numerical decay beyond root parameter twenty-eight

Endpoint logarithm bounds and damped-monomial monotonicity control an
entire ray. The fourth and fifth moments match the smoothing cost and
the scalar zero kernels after multiplication by log(x)^2.
-/

namespace PrimeFactorUnimodality

open Real

/-- The relative exponential smoothing step is uniformly small on this ray. -/
theorem dusartFar_exp_step_le {X : ℝ} (hX : 28 ≤ X) :
    exp (-(4 / 5 : ℝ) * X) ≤ (1 / 5000000000 : ℝ) := by
  have hlog : Real.log (5000000000 : ℝ) ≤ (112 / 5 : ℝ) := by
    rw [show (5000000000 : ℝ) = 5 * 10 ^ 9 by norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2, Real.log_five_lt_d9]
  calc
    _ ≤ exp (-Real.log (5000000000 : ℝ)) := exp_le_exp.mpr (by linarith)
    _ = _ := by rw [exp_neg, exp_log (by norm_num)]; norm_num

/-- The window exponential has a simple rational bound at the same endpoint. -/
theorem dusartFar_exp_window_le {X : ℝ} (hX : 28 ≤ X) :
    exp (-(5 / 4 : ℝ) * X) ≤ (1 / 10 ^ 15 : ℝ) := by
  have hlog : Real.log ((10 : ℝ) ^ 15) ≤ 35 := by
    rw [Real.log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2]
  calc
    _ ≤ exp (-Real.log ((10 : ℝ) ^ 15)) := exp_le_exp.mpr (by
      norm_num at hlog ⊢
      linarith)
    _ = _ := by rw [exp_neg, exp_log (by positivity)]; norm_num

/-- The exponentially growing cutoff includes the billion-height low-zero block. -/
theorem dusartFar_cutoff_ge_billion {X : ℝ} (hX : 28 ≤ X) :
    (1000000000 : ℝ) ≤ exp ((4 / 5 : ℝ) * X) := by
  have hlog : Real.log (1000000000 : ℝ) ≤ 21 := by
    rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, Real.log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2]
  exact (exp_le_exp.mpr (by linarith : Real.log (1000000000 : ℝ) ≤ (4 / 5 : ℝ) * X)).trans_eq'
    (exp_log (by norm_num))

/-- The full smoothing cost fits within one hundredth of the reciprocal log square. -/
theorem dusartFar_smoothing_moment_le {X : ℝ} (hX : 28 ≤ X) :
    36 * X ^ 4 * ((3 / 2 : ℝ) * exp (-(4 / 5 : ℝ) * X)) ≤ (1 / 100 : ℝ) := by
  have hm := Real.pow_mul_exp_neg_le_of_le 4 (by norm_num : (0 : ℝ) < 4 / 5)
    (by norm_num : (4 : ℝ) / (4 / 5) ≤ 28) hX
  have he := dusartFar_exp_step_le (X := 28) le_rfl
  have hp := hm.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 28 ^ 4))
  nlinarith only [hp]

/-- The complete high-tail coefficient has a uniform fifth-moment allowance. -/
theorem dusartFar_high_moment_le {X : ℝ} (hX : 28 ≤ X) :
    36 * X ^ 4 * (2048 * X * exp (-(5 / 4 : ℝ) * X)) ≤ (1 / 500 : ℝ) := by
  have hm := Real.pow_mul_exp_neg_le_of_le 5 (by norm_num : (0 : ℝ) < 5 / 4)
    (by norm_num : (5 : ℝ) / (5 / 4) ≤ 28) hX
  have he := dusartFar_exp_window_le (X := 28) le_rfl
  have hp := hm.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 28 ^ 5))
  nlinarith only [hp]

/-- The smaller finite-window contribution fits in the same allowance. -/
theorem dusartFar_window_moment_le {X : ℝ} (hX : 28 ≤ X) :
    36 * X ^ 4 * (32 * X * exp (-(5 / 4 : ℝ) * X)) ≤ (1 / 500 : ℝ) := by
  have hp := dusartFar_high_moment_le hX
  have hXpos : 0 < X := by linarith
  nlinarith only [hp, mul_pos (pow_pos hXpos 5) (exp_pos (-(5 / 4 : ℝ) * X))]

/-- The low block's half-logarithmic decay has a uniform square-log moment bound. -/
theorem dusartFar_low_moment_le {b : ℝ} (hb : 4704 ≤ b) :
    b ^ 2 * (77 * exp (-b / 2)) ≤ (1 / 500 : ℝ) := by
  have hbpos : 0 < b := by linarith
  have hp := dusartLog_half_exp_le hbpos
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4704) hb 2
  calc
    _ ≤ b ^ 2 * (77 * (384 / b ^ 4)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = 29568 / b ^ 2 := by field_simp; ring
    _ ≤ _ := (div_le_iff₀ (pow_pos hbpos 2)).mpr (by linarith)

/-- The endpoint and trivial-zero correction decays faster than the same square-log scale. -/
theorem dusartFar_correction_moment_le {b : ℝ} (hb : 4704 ≤ b) :
    b ^ 2 * (4 / exp b) ≤ (1 / 1000 : ℝ) := by
  have hbpos : 0 < b := by linarith
  have he := Real.pow_div_factorial_le_exp b hbpos.le 4
  norm_num at he
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4704) hb 2
  calc
    _ ≤ b ^ 2 * (4 / (b ^ 4 / 24)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) he) (by positivity)
    _ = 96 / b ^ 2 := by field_simp; ring
    _ ≤ _ := (div_le_iff₀ (pow_pos hbpos 2)).mpr (by linarith)

end PrimeFactorUnimodality
