import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds

/-! # Explicit low-mass and sixth-power bounds at a reduced cutoff

The half-total positive-prefix mass and the proved counting primitive
control the inner height 1250000. Elementary logarithm bounds evaluate
the sixth-power tails there and at 25000000. These estimates do not
assume a numerical zero-location or sign computation.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The reciprocal-counting window has a closed logarithmic polynomial form. -/
theorem xiReciprocalNormWindowBound_eq_logs {a U : ℝ} (ha : 0 < a) (hU : 0 < U) :
    xiReciprocalNormWindowBound a U =
      (log U ^ 2 - log a ^ 2 - 2 * log (2 * π) * (log U - log a) +
        2 * log a - 2 * log (2 * π) - 2) / (4 * π) + (log a + 18) / a - 1 / U := by
  unfold xiReciprocalNormWindowBound xiReciprocalCountEnvelope xiZeroCountingMainTerm
    xiReciprocalCountPrimitive
  rw [log_div hU.ne' (by positivity : 2 * π ≠ 0),
    log_div ha.ne' (by positivity : 2 * π ≠ 0)]
  field_simp
  ring

/-- The small prefix height has explicit rational logarithm bounds. -/
theorem dusart_log_twenty_five_bounds : (3218 / 1000 : ℝ) ≤ log 25 ∧
    log 25 ≤ (3219 / 1000 : ℝ) := by
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, log_pow]
  norm_num
  constructor <;> linarith [log_five_gt_d9, log_five_lt_d9]

/-- Exact factorization supplies both sides of the inner-height logarithm. -/
theorem dusart_log_inner_reduced_bounds : (14038 / 1000 : ℝ) ≤ log 1250000 ∧
    log 1250000 ≤ (14039 / 1000 : ℝ) := by
  rw [show (1250000 : ℝ) = 2 ^ 4 * 5 ^ 7 by norm_num,
    log_mul (by norm_num : (2 : ℝ) ^ 4 ≠ 0) (by norm_num : (5 : ℝ) ^ 7 ≠ 0),
    log_pow, log_pow]
  norm_num
  constructor <;> linarith [log_two_gt_d9, log_two_lt_d9, log_five_gt_d9, log_five_lt_d9]

/-- The outer-height logarithm has proved rational bounds on both sides. -/
theorem dusart_log_outer_reduced_bounds : (17034 / 1000 : ℝ) ≤ log 25000000 ∧
    log (25000000 : ℝ) ≤ 17035 / 1000 := by
  rw [show (25000000 : ℝ) = 2 ^ 6 * 5 ^ 8 by norm_num,
    log_mul (by norm_num : (2 : ℝ) ^ 6 ≠ 0) (by norm_num : (5 : ℝ) ^ 8 ≠ 0),
    log_pow, log_pow]
  norm_num
  constructor <;> linarith [log_two_gt_d9, log_two_lt_d9, log_five_gt_d9, log_five_lt_d9]

/-- The complete reciprocal window has a rational bound without enumerating zeros. -/
theorem xiReciprocalNormWindowBound_reduced_le :
    xiReciprocalNormWindowBound 25 1250000 ≤ (12613 / 1000 : ℝ) := by
  let L := log (1250000 : ℝ)
  let A := log (25 : ℝ)
  let B := log (2 * π)
  have hL : (14038 / 1000 : ℝ) ≤ L := dusart_log_inner_reduced_bounds.1
  have hL' : L ≤ (14039 / 1000 : ℝ) := dusart_log_inner_reduced_bounds.2
  have hA : (3218 / 1000 : ℝ) ≤ A := dusart_log_twenty_five_bounds.1
  have hA' : A ≤ (3219 / 1000 : ℝ) := dusart_log_twenty_five_bounds.2
  have hB : (1837 / 1000 : ℝ) ≤ B := log_two_mul_pi_gt_1837_div_1000.le
  let N : ℝ := (14039 / 1000 : ℝ) ^ 2 - (3218 / 1000 : ℝ) ^ 2 -
    2 * (1837 / 1000) * (14038 / 1000 - 3219 / 1000) +
      2 * (3219 / 1000) - 2 * (1837 / 1000) - 2
  have hN : L ^ 2 - A ^ 2 - 2 * B * (L - A) + 2 * A - 2 * B - 2 ≤ N := by
    have hsL : L ^ 2 ≤ (14039 / 1000 : ℝ) ^ 2 := by nlinarith
    have hsA : (3218 / 1000 : ℝ) ^ 2 ≤ A ^ 2 := by nlinarith
    have hp : (1837 / 1000 : ℝ) * (14038 / 1000 - 3219 / 1000) ≤ B * (L - A) :=
      mul_le_mul hB (by linarith) (by norm_num) (by linarith)
    dsimp only [N]
    nlinarith only [hsL, hsA, hp, hA', hB]
  have hfrac : (L ^ 2 - A ^ 2 - 2 * B * (L - A) + 2 * A - 2 * B - 2) / (4 * π) ≤
      N / (4 * (314 / 100 : ℝ)) := by
    exact (div_le_div_of_nonneg_right hN (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num [N]) (by norm_num) (by linarith [pi_gt_d2]))
  rw [xiReciprocalNormWindowBound_eq_logs (by norm_num) (by norm_num)]
  change (L ^ 2 - A ^ 2 - 2 * B * (L - A) + 2 * A - 2 * B - 2) / (4 * π) +
    (A + 18) / 25 - 1 / 1250000 ≤ _
  dsimp only [N] at hfrac
  linarith

/-- The actual low-block expression benefits from the half-total prefix mass. -/
theorem xiLowReciprocalNormBound_reduced_le :
    xiLowReciprocalNormBound 25 1250000 (1 / 2) ≤ (13393 / 500 : ℝ) := by
  have hp : ((25 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - log (4 * π)) / 4) ≤ 78 / 100 := by
    linarith [xiRealReciprocalMass_lt_three_hundredths]
  have hm := (min_le_right (xiReciprocalCountEnvelope 25 / (1 / 2))
    (((25 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - log (4 * π)) / 4))).trans hp
  unfold xiLowReciprocalNormBound
  linarith [xiReciprocalNormWindowBound_reduced_le]

/-- Order six has an exact rational-logarithmic tail expression. -/
theorem xiRosserPowerTailBound_six_eq {U : ℝ} (hU : 0 < U) :
    xiRosserPowerTailBound 6 U =
      (5 * log (U / (2 * π)) + 1) / (25 * π * U ^ 5) +
        (4 * log U + 205 / 3) / U ^ 6 := by
  unfold xiRosserPowerTailBound logDampedPowerIntegralFactor
  rw [logDampedPower_eq_rpow_mul hU]
  norm_num only [show (1 - 6 : ℝ) = -5 by norm_num, neg_zero, zero_div, Real.exp_zero, mul_one]
  rw [Real.rpow_neg hU.le, Real.rpow_neg hU.le]
  norm_cast
  ring

/-- A logarithm enclosure controls the entire sixth-power tail. -/
theorem xiRosserPowerTailBound_six_le_log_bound {U L : ℝ} (hU : 0 < U)
    (hL : 2 ≤ L) (hlog : log U ≤ L) :
    xiRosserPowerTailBound 6 U ≤
      (5 * L - 5 * (1837 / 1000 : ℝ) + 1) / (25 * (314 / 100 : ℝ) * U ^ 5) +
        (4 * L + 205 / 3) / U ^ 6 := by
  rw [xiRosserPowerTailBound_six_eq hU, log_div hU.ne' (by positivity)]
  apply add_le_add
  · exact (div_le_div_of_nonneg_right
      (by linarith [log_two_mul_pi_gt_1837_div_1000]) (by positivity)).trans
      (div_le_div_of_nonneg_left (by linarith) (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith [pi_gt_d2]) (by positivity)))
  · exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The inner sixth-power tail has a rational upper bound. -/
theorem xiRosserPowerTailBound_six_inner_reduced_le :
    xiRosserPowerTailBound 6 1250000 ≤ (26 / 10 ^ 32 : ℝ) :=
  (xiRosserPowerTailBound_six_le_log_bound (by norm_num) (by norm_num)
    dusart_log_inner_reduced_bounds.2).trans (by norm_num)

/-- The outer sixth-power tail has a rational upper bound. -/
theorem xiRosserPowerTailBound_six_outer_reduced_le :
    xiRosserPowerTailBound 6 25000000 ≤ (102 / 10 ^ 39 : ℝ) :=
  (xiRosserPowerTailBound_six_le_log_bound (by norm_num) (by norm_num)
    dusart_log_outer_reduced_bounds.2).trans (by norm_num)

end

end PrimeFactorUnimodality
