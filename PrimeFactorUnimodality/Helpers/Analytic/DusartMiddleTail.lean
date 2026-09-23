import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds

/-! # The fixed billion-height tail across the middle logarithmic band

Keep the full fourth height power, splitting off only the integrable
square power. The selected coefficient is the cutoff branch throughout
this band. Its remaining exponential damping and rational coefficient
give an explicit bound for the existing complete Rosser tail expression.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The fixed cutoff logarithm lies in a short rational interval. -/
theorem dusartMiddle_log_billion_bounds :
    (207 / 10 : ℝ) ≤ Real.log 1000000000 ∧ Real.log 1000000000 ≤ 21 := by
  have he : Real.log (1000000000 : ℝ) = 9 * Real.log 10 := by
    rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, Real.log_pow]
    norm_num
  constructor <;> linarith [dusart_log_ten_bounds.1, dusart_log_ten_bounds.2]

/-- The cutoff remains beyond the remaining kernel's turning point through log height 5000. -/
theorem dusartMiddle_cutoff_branch {b : ℝ} (hb : b ≤ 5000) :
    exp (sqrt ((b / 6) / (4 - 2))) ≤ (1000000000 : ℝ) := by
  have hl := dusartMiddle_log_billion_bounds.1
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 207 / 10) hl 2
  have hroot : sqrt ((b / 6) / (4 - 2)) ≤ Real.log 1000000000 := by
    apply (sqrt_le_left (by linarith)).mpr
    norm_num
    linarith
  exact (exp_le_exp.mpr hroot).trans_eq (exp_log (by norm_num))

/-- The closed expression retains the exact exponential factor and full height power. -/
theorem xiRosserClosedTailBound_four_two_eq {b U : ℝ} (hU : 0 < U)
    (hpeak : exp (sqrt ((b / 6) / (4 - 2))) ≤ U) :
    xiRosserClosedTailBound (b / 6) 4 2 U =
      ((Real.log (U / (2 * π)) + 1) / (π * U ^ 3) +
        (4 * Real.log U + 69) / U ^ 4) * exp (-b / (6 * Real.log U)) := by
  unfold xiRosserClosedTailBound logDampedPowerMajorant
  rw [ite_eq_left hpeak]
  norm_num only [show (4 - 2 : ℝ) = 2 by norm_num]
  rw [logDampedPower_eq_rpow_mul hU, logDampedPower_eq_rpow_mul hU]
  unfold logDampedPowerIntegralFactor
  norm_num only [show (1 - 2 : ℝ) = -1 by norm_num,
    show (2 - 1 : ℝ) = 1 by norm_num, div_one, one_pow]
  rw [Real.rpow_neg hU.le, Real.rpow_neg hU.le, Real.rpow_neg hU.le]
  norm_cast
  rw [show -(b / 6) / Real.log U = -b / (6 * Real.log U) by ring]
  ring

/-- The rational coefficient of the billion-height expression is less than seven over H cubed. -/
theorem dusartMiddle_tail_coefficient_le :
    (Real.log ((1000000000 : ℝ) / (2 * π)) + 1) / (π * 1000000000 ^ 3) +
      (4 * Real.log 1000000000 + 69) / 1000000000 ^ 4 ≤ (7 / 10 ^ 27 : ℝ) := by
  have hl := dusartMiddle_log_billion_bounds.2
  have hn : Real.log ((1000000000 : ℝ) / (2 * π)) + 1 ≤ (20163 / 1000 : ℝ) := by
    rw [Real.log_div (by norm_num) (by positivity)]
    linarith [Real.log_two_mul_pi_gt_1837_div_1000]
  have hfirst : (Real.log ((1000000000 : ℝ) / (2 * π)) + 1) / (π * 1000000000 ^ 3) ≤
      (20163 / 1000 : ℝ) / (3 * 1000000000 ^ 3) := by
    calc
      _ ≤ (20163 / 1000 : ℝ) / (π * 1000000000 ^ 3) :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by nlinarith [pi_gt_three])
  have hsecond : (4 * Real.log 1000000000 + 69) / (1000000000 : ℝ) ^ 4 ≤
      153 / (1000000000 : ℝ) ^ 4 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
  exact (add_le_add hfirst hsecond).trans (by norm_num)

/-- The whole scalar tail is bounded uniformly, with its damping still visible. -/
theorem xiRosserClosedTailBound_middle_le {b : ℝ} (hb : 0 ≤ b) (hb₁ : b ≤ 5000) :
    xiRosserClosedTailBound (b / 6) 4 2 1000000000 ≤
      (7 / 10 ^ 27 : ℝ) * exp (-b / 126) := by
  have hl := dusartMiddle_log_billion_bounds
  have hd : b / 126 ≤ b / (6 * Real.log 1000000000) :=
    div_le_div_of_nonneg_left hb (by linarith) (by linarith)
  rw [xiRosserClosedTailBound_four_two_eq (by norm_num) (dusartMiddle_cutoff_branch hb₁)]
  calc
    _ ≤ (7 / 10 ^ 27 : ℝ) * exp (-b / (6 * Real.log 1000000000)) :=
      mul_le_mul_of_nonneg_right dusartMiddle_tail_coefficient_le (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hd)) (by norm_num)

end

end PrimeFactorUnimodality
