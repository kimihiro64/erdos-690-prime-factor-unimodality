import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalNormBound
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserClosedBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.PiBounds
import PrimeFactorUnimodality.Mathlib.NumberTheory.Harmonic.EulerMascheroniBounds

/-! # Explicit scalar constants for the zero-sum estimates

The real mass, reciprocal window and two power-tail values are proved
from elementary bounds. No numerical scalar hypothesis remains in
these statements. This does not supply any low-zero location data.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The unconditional exact real reciprocal mass is below 0.03. -/
theorem xiRealReciprocalMass_lt_three_hundredths :
    (2 + eulerMascheroniConstant - Real.log (4 * π)) / 2 <
    (3 / 100 : ℝ) := by
  linarith [eulerMascheroniConstant_lt_59_div_100, log_four_mul_pi_gt_5061_div_2000]

/-- Coarse rational bounds suffice for the selected height logarithms. -/
theorem dusart_log_ten_bounds : (2302 / 1000 : ℝ) ≤ Real.log 10 ∧
    Real.log 10 ≤ (2303 / 1000 : ℝ) := by
  have h : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  constructor <;> linarith [log_two_gt_d9, log_two_lt_d9, log_five_gt_d9, log_five_lt_d9]

/-- The entire reciprocal-counting window has this rational bound. -/
theorem xiReciprocalNormWindowBound_million_le :
    xiReciprocalNormWindowBound 10 1000000 ≤ (2673 / 200 : ℝ) := by
  let L := Real.log 10
  let B := Real.log (2 * π)
  have hL : (2302 / 1000 : ℝ) ≤ L := dusart_log_ten_bounds.1
  have hL' : L ≤ (2303 / 1000 : ℝ) := dusart_log_ten_bounds.2
  have hB : (1837 / 1000 : ℝ) ≤ B := log_two_mul_pi_gt_1837_div_1000.le
  have hπ : (314 / 100 : ℝ) ≤ π := by linarith [pi_gt_d2]
  have hl : Real.log (1000000 : ℝ) = 6 * L := by
    rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num, log_pow]
    norm_num
    rfl
  have he : xiReciprocalNormWindowBound 10 1000000 =
      (35 * L ^ 2 - 10 * L * B + 2 * L - 2 * B - 2) / (4 * π) +
        (L + 18) / 10 - 1 / 1000000 := by
    unfold xiReciprocalNormWindowBound xiReciprocalCountEnvelope xiZeroCountingMainTerm
      xiReciprocalCountPrimitive
    rw [log_div (by norm_num : (1000000 : ℝ) ≠ 0) (by positivity : 2 * π ≠ 0),
      log_div (by norm_num : (10 : ℝ) ≠ 0) (by positivity : 2 * π ≠ 0), hl]
    dsimp [L, B]
    ring
  let N : ℝ := 35 * (2303 / 1000 : ℝ) ^ 2 - 10 * (2302 / 1000 : ℝ) *
    (1837 / 1000 : ℝ) + 2 * (2303 / 1000 : ℝ) - 2 * (1837 / 1000 : ℝ) - 2
  have hN : 35 * L ^ 2 - 10 * L * B + 2 * L - 2 * B - 2 ≤ N := by
    have hs : L ^ 2 ≤ (2303 / 1000 : ℝ) ^ 2 := by nlinarith
    have hp : (2302 / 1000 : ℝ) * (1837 / 1000 : ℝ) ≤ L * B :=
      mul_le_mul hL hB (by norm_num) (by linarith)
    dsimp [N]
    nlinarith
  have hfrac : (35 * L ^ 2 - 10 * L * B + 2 * L - 2 * B - 2) / (4 * π) ≤
      N / (4 * (314 / 100 : ℝ)) := by
    calc
      _ ≤ N / (4 * π) := div_le_div_of_nonneg_right hN (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num [N]) (by norm_num)
        (by linarith)
  rw [he]
  dsimp [N] at hfrac
  linarith

/-- The refined low-block expression is bounded at the selected inner height. -/
theorem xiLowReciprocalNormBound_million_half_le : xiLowReciprocalNormBound 10 1000000 (1 / 2) ≤
    (561 / 20 : ℝ) := by
  have hp : ((10 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - Real.log (4 * π)) / 2) ≤ 66 / 100 := by
    linarith [xiRealReciprocalMass_lt_three_hundredths]
  have hm := (min_le_right (xiReciprocalCountEnvelope 10 / (1 / 2))
    (((10 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - Real.log (4 * π)) / 2))).trans hp
  unfold xiLowReciprocalNormBound
  linarith [xiReciprocalNormWindowBound_million_le]

/-- At order four the real-power expression has a rational-logarithmic form. -/
theorem xiRosserPowerTailBound_four_eq {U : ℝ} (hU : 0 < U) :
    xiRosserPowerTailBound 4 U =
      (3 * Real.log (U / (2 * π)) + 1) / (9 * π * U ^ 3) +
        (4 * Real.log U + 137 / 2) / U ^ 4 := by
  unfold xiRosserPowerTailBound logDampedPowerIntegralFactor
  rw [logDampedPower_eq_rpow_mul hU]
  norm_num only [show (1 - 4 : ℝ) = -3 by norm_num, neg_zero, zero_div, Real.exp_zero, mul_one]
  rw [Real.rpow_neg hU.le, Real.rpow_neg hU.le]
  norm_cast
  ring

/-- A logarithm upper bound gives a rational upper bound for any height. -/
theorem xiRosserPowerTailBound_four_le_log_bound {U L : ℝ} (hU : 0 < U) (hL : 2 ≤ L)
    (hlog : Real.log U ≤ L) :
    xiRosserPowerTailBound 4 U ≤
      (3 * L - 3 * (1837 / 1000 : ℝ) + 1) / (9 * (314 / 100 : ℝ) * U ^ 3) +
        (4 * L + 137 / 2) / U ^ 4 := by
  rw [xiRosserPowerTailBound_four_eq hU, Real.log_div hU.ne' (by positivity)]
  apply add_le_add
  · calc
      _ ≤ (3 * L - 3 * (1837 / 1000 : ℝ) + 1) / (9 * π * U ^ 3) :=
        div_le_div_of_nonneg_right (by linarith [log_two_mul_pi_gt_1837_div_1000]) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith [pi_gt_d2]) (by positivity))
  · exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The full fourth-power tail is small at the inner height. -/
theorem xiRosserPowerTailBound_four_million_le : xiRosserPowerTailBound 4 1000000 ≤
    (131 / 10 ^ 20 : ℝ) := by
  have hl : Real.log (1000000 : ℝ) ≤ 6 * (2303 / 1000 : ℝ) := by
    rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num, Real.log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2]
  exact (xiRosserPowerTailBound_four_le_log_bound
    (by norm_num) (by norm_num) hl).trans (by norm_num)

/-- The full fourth-power tail is small at the outer height. -/
theorem xiRosserPowerTailBound_four_billion_le : xiRosserPowerTailBound 4 1000000000 ≤
    (205 / 10 ^ 29 : ℝ) := by
  have hl : Real.log (1000000000 : ℝ) ≤ 9 * (2303 / 1000 : ℝ) := by
    rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, Real.log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2]
  exact (xiRosserPowerTailBound_four_le_log_bound
    (by norm_num) (by norm_num) hl).trans (by norm_num)

/-- The cubic power tail at the outer height has a rational bound. -/
theorem xiRosserPowerTailBound_three_billion_le : xiRosserPowerTailBound 3 1000000000 ≤
    (4 / 10 ^ 18 : ℝ) := by
  have he : xiRosserPowerTailBound 3 1000000000 =
      (2 * Real.log ((1000000000 : ℝ) / (2 * π)) + 1) / (4 * π * 1000000000 ^ 2) +
        (4 * Real.log (1000000000 : ℝ) + 206 / 3) / 1000000000 ^ 3 := by
    unfold xiRosserPowerTailBound logDampedPowerIntegralFactor
    rw [logDampedPower_eq_rpow_mul (by norm_num : (0 : ℝ) < 1000000000)]
    norm_num only [show (1 - 3 : ℝ) = -2 by norm_num, neg_zero, zero_div,
      Real.exp_zero, mul_one]
    ring
  have hl : Real.log (1000000000 : ℝ) ≤ 9 * (2303 / 1000 : ℝ) := by
    rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, Real.log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2]
  have hn : 2 * Real.log ((1000000000 : ℝ) / (2 * π)) + 1 ≤ 40 := by
    rw [Real.log_div (by norm_num) (by positivity)]
    linarith [Real.log_two_mul_pi_gt_1837_div_1000]
  have hfirst : (2 * Real.log ((1000000000 : ℝ) / (2 * π)) + 1) /
      (4 * π * 1000000000 ^ 2) ≤ 40 / (4 * 3 * 1000000000 ^ 2 : ℝ) := by
    calc
      _ ≤ 40 / (4 * π * 1000000000 ^ 2) :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by nlinarith [pi_gt_three])
  have hsecond : (4 * Real.log (1000000000 : ℝ) + 206 / 3) / 1000000000 ^ 3 ≤
      160 / (1000000000 ^ 3 : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  rw [he]
  exact (add_le_add hfirst hsecond).trans (by norm_num)

/-- A coarse rational bound on the full reciprocal window to the outer height. -/
theorem xiReciprocalNormWindowBound_billion_le :
    xiReciprocalNormWindowBound 10 1000000000 ≤ (1717 / 50 : ℝ) := by
  let L := Real.log 10
  let B := Real.log (2 * π)
  have hL : (2302 / 1000 : ℝ) ≤ L := dusart_log_ten_bounds.1
  have hL' : L ≤ (2303 / 1000 : ℝ) := dusart_log_ten_bounds.2
  have hB : (1837 / 1000 : ℝ) ≤ B := log_two_mul_pi_gt_1837_div_1000.le
  have hπ : (314 / 100 : ℝ) ≤ π := by linarith [pi_gt_d2]
  have hl : Real.log (1000000000 : ℝ) = 9 * L := by
    rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, log_pow]
    norm_num
    rfl
  have he : xiReciprocalNormWindowBound 10 1000000000 =
      (80 * L ^ 2 - 16 * L * B + 2 * L - 2 * B - 2) / (4 * π) +
        (L + 18) / 10 - 1 / 1000000000 := by
    unfold xiReciprocalNormWindowBound xiReciprocalCountEnvelope xiZeroCountingMainTerm
      xiReciprocalCountPrimitive
    rw [log_div (by norm_num : (1000000000 : ℝ) ≠ 0) (by positivity : 2 * π ≠ 0),
      log_div (by norm_num : (10 : ℝ) ≠ 0) (by positivity : 2 * π ≠ 0), hl]
    dsimp [L, B]
    ring
  let N : ℝ := 80 * (2303 / 1000 : ℝ) ^ 2 - 16 * (2302 / 1000 : ℝ) *
    (1837 / 1000 : ℝ) + 2 * (2303 / 1000 : ℝ) - 2 * (1837 / 1000 : ℝ) - 2
  have hN : 80 * L ^ 2 - 16 * L * B + 2 * L - 2 * B - 2 ≤ N := by
    have hs : L ^ 2 ≤ (2303 / 1000 : ℝ) ^ 2 := by nlinarith
    have hp : (2302 / 1000 : ℝ) * (1837 / 1000 : ℝ) ≤ L * B :=
      mul_le_mul hL hB (by norm_num) (by linarith)
    dsimp [N]
    nlinarith
  have hfrac : (80 * L ^ 2 - 16 * L * B + 2 * L - 2 * B - 2) / (4 * π) ≤
      N / (4 * (314 / 100 : ℝ)) := by
    calc
      _ ≤ N / (4 * π) := div_le_div_of_nonneg_right hN (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num [N]) (by norm_num)
        (by linarith)
  rw [he]
  dsimp [N] at hfrac
  linarith

/-- The low-block expression at the outer height is at most seventy. -/
theorem xiLowReciprocalNormBound_billion_half_le : xiLowReciprocalNormBound 10 1000000000 (1 / 2) ≤
    (70 : ℝ) := by
  have hp : ((10 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - Real.log (4 * π)) / 2) ≤ 66 / 100 := by
    linarith [xiRealReciprocalMass_lt_three_hundredths]
  have hm := (min_le_right (xiReciprocalCountEnvelope 10 / (1 / 2))
    (((10 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - Real.log (4 * π)) / 2))).trans hp
  unfold xiLowReciprocalNormBound
  linarith [xiReciprocalNormWindowBound_billion_le]

end

end PrimeFactorUnimodality
