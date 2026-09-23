import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleTail
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Exp.Monomial

/-! # Uniform square-log moments for the middle-range smoothing budget

The complete high coefficient reduces to an eighth-degree damped monomial.
Its global maximum, not only its decreasing ray, controls every logarithmic
base point. The low and elementary correction terms have much smaller
allowances, while the smoothing step ranges over a short explicit interval.
-/

namespace PrimeFactorUnimodality

open Real

private theorem middle_exp_neg_eight_le : exp (-8 : ℝ) ≤ (1 / 2500 : ℝ) := by
  have hl : Real.log (2500 : ℝ) ≤ 8 := by
    rw [show (2500 : ℝ) = 2 ^ 2 * 5 ^ 4 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  calc
    _ ≤ exp (-Real.log (2500 : ℝ)) := exp_le_exp.mpr (by linarith)
    _ = _ := by rw [exp_neg, exp_log (by norm_num)]; norm_num

/-- The eighth-degree moment is uniformly bounded on both sides of its turning point. -/
theorem dusartMiddle_eighth_moment_le {b : ℝ} (hb : 0 ≤ b) :
    b ^ 8 * exp (-b / 126) ≤ (1008 : ℝ) ^ 8 / 2500 := by
  have hm : b ^ 8 * exp (-b / 126) ≤ (1008 : ℝ) ^ 8 * exp (-8) := by
    have h := Real.pow_mul_exp_neg_le_peak 8 (by norm_num)
      (by norm_num : (0 : ℝ) < 1 / 126) hb
    simp only [Nat.cast_ofNat, show (8 : ℝ) / (1 / 126) = 1008 by norm_num] at h
    simpa only [show -(1 / 126 : ℝ) * b = -b / 126 by ring] using h
  exact hm.trans ((mul_le_mul_of_nonneg_left middle_exp_neg_eight_le
    (by norm_num : (0 : ℝ) ≤ 1008 ^ 8)).trans_eq (by ring))

/-- The smoothing window leaves the total width extremely close to one. -/
theorem dusartMiddle_width_le {b s : ℝ} (hb : 84 ≤ b)
    (hs : s ≤ (17 / 200 : ℝ) / b ^ 2) : 1 + 3 * s ≤ (10001 / 10000 : ℝ) := by
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 84) hb 2
  have hmax := hs.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq)
  linarith

/-- The full cubic smoothing coefficient is controlled by the lower end of the step window. -/
theorem dusartMiddle_high_coefficient_le {b s : ℝ} (hb : 84 ≤ b)
    (hs₀ : (3 / 40 : ℝ) / b ^ 2 ≤ s) (hs₁ : s ≤ (17 / 200 : ℝ) / b ^ 2) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ (202 / 25 : ℝ) / ((3 / 40 : ℝ) / b ^ 2) ^ 3 := by
  have hbpos : 0 < b := by linarith
  have hspos : 0 < s := (by positivity : 0 < (3 / 40 : ℝ) / b ^ 2).trans_le hs₀
  have hw : (1 + 3 * s) ^ 4 ≤ (101 / 100 : ℝ) :=
    (pow_le_pow_left₀ (by positivity) (dusartMiddle_width_le hb hs₁) 4).trans (by norm_num)
  calc
    _ ≤ (202 / 25 : ℝ) / s ^ 3 := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity) hs₀ 3)

/-- The entire high-tail contribution fits into its square-log allowance. -/
theorem dusartMiddle_high_moment_le {b s : ℝ} (hb : 84 ≤ b) (hb₁ : b ≤ 5000)
    (hs₀ : (3 / 40 : ℝ) / b ^ 2 ≤ s) (hs₁ : s ≤ (17 / 200 : ℝ) / b ^ 2) :
    b ^ 2 * ((8 * (1 + 3 * s) ^ 4 / s ^ 3) *
      xiRosserClosedTailBound (b / 6) 4 2 1000000000) ≤ (59 / 1000 : ℝ) := by
  have hbpos : 0 < b := by linarith
  have hspos : 0 < s := (by positivity : 0 < (3 / 40 : ℝ) / b ^ 2).trans_le hs₀
  have hc := dusartMiddle_high_coefficient_le hb hs₀ hs₁
  have ht := xiRosserClosedTailBound_middle_le hbpos.le hb₁
  let C : ℝ := (202 / 25) / (3 / 40) ^ 3 * (7 / 10 ^ 27)
  calc
    _ ≤ b ^ 2 * ((8 * (1 + 3 * s) ^ 4 / s ^ 3) *
        ((7 / 10 ^ 27 : ℝ) * exp (-b / 126))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by positivity)) (by positivity)
    _ ≤ b ^ 2 * (((202 / 25 : ℝ) / ((3 / 40 : ℝ) / b ^ 2) ^ 3) *
        ((7 / 10 ^ 27 : ℝ) * exp (-b / 126))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ = C * (b ^ 8 * exp (-b / 126)) := by dsimp [C]; field_simp
    _ ≤ C * ((1008 : ℝ) ^ 8 / 2500) :=
      mul_le_mul_of_nonneg_left (dusartMiddle_eighth_moment_le hbpos.le) (by norm_num [C])
    _ ≤ _ := by norm_num [C]

private theorem middle_exp_neg_forty_two_le : exp (-42 : ℝ) ≤ (1 / 10 ^ 18 : ℝ) := by
  have hl : Real.log ((10 : ℝ) ^ 18) ≤ 42 := by
    rw [Real.log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2]
  calc
    _ ≤ exp (-Real.log ((10 : ℝ) ^ 18)) := exp_le_exp.mpr (by norm_num at hl ⊢; linarith)
    _ = _ := by rw [exp_neg, exp_log (by positivity)]; norm_num

/-- The normalized low-zero block has a negligible square-log moment throughout the middle band. -/
theorem dusartMiddle_low_moment_le {b : ℝ} (hb : 84 ≤ b) :
    b ^ 2 * (77 * exp (-b / 2)) ≤ (1 / 10000 : ℝ) := by
  have hm := Real.pow_mul_exp_neg_le_of_le 2 (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (2 : ℝ) / (1 / 2) ≤ 84) hb
  have he : exp (-(1 / 2 : ℝ) * 84) ≤ (1 / 10 ^ 18 : ℝ) := by
    simpa only [show -(1 / 2 : ℝ) * 84 = -42 by norm_num] using middle_exp_neg_forty_two_le
  have hh := hm.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 84 ^ 2))
  rw [show -(1 / 2 : ℝ) * b = -b / 2 by ring] at hh
  nlinarith only [hh]

/-- The normalized elementary correction fits in the same small allowance. -/
theorem dusartMiddle_correction_moment_le {b : ℝ} (hb : 84 ≤ b) :
    b ^ 2 * (4 / exp b) ≤ (1 / 10000 : ℝ) := by
  have he : exp (-b) ≤ exp (-b / 2) := exp_le_exp.mpr (by linarith)
  calc
    _ = b ^ 2 * (4 * exp (-b)) := by rw [exp_neg]; ring
    _ ≤ b ^ 2 * (77 * exp (-b / 2)) := mul_le_mul_of_nonneg_left
      (by linarith [exp_pos (-b / 2)]) (sq_nonneg b)
    _ ≤ _ := dusartMiddle_low_moment_le hb

end PrimeFactorUnimodality
