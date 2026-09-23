import PrimeFactorUnimodality.Helpers.Analytic.XiReducedCutoffBounds

/-! # Scalar bounds for an earlier finite-to-analytic transition

The same proved reciprocal-mass and complete-tail formulas are evaluated at
inner height 100000 and outer height 25000000. Every constant is obtained by
exact rational arithmetic from elementary logarithm bounds; no zero-location
or prime-counting computation occurs here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Bounds for the new inner-height logarithm follow from its exact power of ten. -/
theorem dusart_log_early_inner_bounds : (1151 / 100 : ℝ) ≤ log 100000 ∧
    log 100000 ≤ (2303 / 200 : ℝ) := by
  rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, log_pow]
  norm_num
  constructor <;> linarith [dusart_log_ten_bounds.1, dusart_log_ten_bounds.2]

/-- The entire reciprocal window has a rational upper bound at the earlier inner height. -/
theorem xiReciprocalNormWindowBound_early_le :
    xiReciprocalNormWindowBound 25 100000 ≤ (83 / 10 : ℝ) := by
  let L := log (100000 : ℝ)
  let A := log (25 : ℝ)
  let B := log (2 * π)
  have hL : (1151 / 100 : ℝ) ≤ L := dusart_log_early_inner_bounds.1
  have hL' : L ≤ (2303 / 200 : ℝ) := dusart_log_early_inner_bounds.2
  have hA : (3218 / 1000 : ℝ) ≤ A := dusart_log_twenty_five_bounds.1
  have hA' : A ≤ (3219 / 1000 : ℝ) := dusart_log_twenty_five_bounds.2
  have hB : (1837 / 1000 : ℝ) ≤ B := log_two_mul_pi_gt_1837_div_1000.le
  let N : ℝ := (2303 / 200 : ℝ) ^ 2 - (3218 / 1000 : ℝ) ^ 2 -
    2 * (1837 / 1000) * (1151 / 100 - 3219 / 1000) +
      2 * (3219 / 1000) - 2 * (1837 / 1000) - 2
  have hN : L ^ 2 - A ^ 2 - 2 * B * (L - A) + 2 * A - 2 * B - 2 ≤ N := by
    have hsL : L ^ 2 ≤ (2303 / 200 : ℝ) ^ 2 := by nlinarith
    have hsA : (3218 / 1000 : ℝ) ^ 2 ≤ A ^ 2 := by nlinarith
    have hp : (1837 / 1000 : ℝ) * (1151 / 100 - 3219 / 1000) ≤ B * (L - A) :=
      mul_le_mul hB (by linarith) (by norm_num) (by linarith)
    dsimp only [N]
    nlinarith only [hsL, hsA, hp, hA', hB]
  have hfrac : (L ^ 2 - A ^ 2 - 2 * B * (L - A) + 2 * A - 2 * B - 2) / (4 * π) ≤
      N / (4 * (314 / 100 : ℝ)) :=
    (div_le_div_of_nonneg_right hN (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num [N]) (by norm_num) (by linarith [pi_gt_d2]))
  rw [xiReciprocalNormWindowBound_eq_logs (by norm_num) (by norm_num)]
  change (L ^ 2 - A ^ 2 - 2 * B * (L - A) + 2 * A - 2 * B - 2) / (4 * π) +
    (A + 18) / 25 - 1 / 100000 ≤ _
  dsimp only [N] at hfrac
  linarith

/-- The positive-prefix mass and full window bound all low reciprocal norms. -/
theorem xiLowReciprocalNormBound_early_le :
    xiLowReciprocalNormBound 25 100000 (1 / 2) ≤ (91 / 5 : ℝ) := by
  have hp : ((25 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - log (4 * π)) / 4) ≤ 78 / 100 := by
    linarith [xiRealReciprocalMass_lt_three_hundredths]
  have hm := (min_le_right (xiReciprocalCountEnvelope 25 / (1 / 2))
    (((25 + 1) / (1 / 2) : ℝ) *
      ((2 + eulerMascheroniConstant - log (4 * π)) / 4))).trans hp
  unfold xiLowReciprocalNormBound
  linarith [xiReciprocalNormWindowBound_early_le]

/-- The inner complete tail controls the smoothed part of the low block. -/
theorem xiRosserPowerTailBound_four_early_inner_le :
    xiRosserPowerTailBound 4 100000 ≤ (11 / 10 ^ 16 : ℝ) :=
  (xiRosserPowerTailBound_four_le_log_bound (by norm_num) (by norm_num)
    dusart_log_early_inner_bounds.2).trans (by norm_num)

/-- The outer complete tail requires no zero-location information above its cutoff. -/
theorem xiRosserPowerTailBound_four_early_outer_le :
    xiRosserPowerTailBound 4 25000000 ≤ (11 / 10 ^ 23 : ℝ) :=
  (xiRosserPowerTailBound_four_le_log_bound (by norm_num) (by norm_num)
    dusart_log_outer_reduced_bounds.2).trans (by norm_num)

end

end PrimeFactorUnimodality
