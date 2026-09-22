import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleMean
import PrimeFactorUnimodality.Helpers.Analytic.BacklundVerticalArgument

/-! # Elementary constants for the averaged Backlund circle

The radius ratio is `5/3`. Existing rational bounds on `exp(1)` prove its
logarithm exceeds `1/2`, and bound the three fixed logarithms. All height
dependence remains symbolic; there is no height enumeration.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The chosen radii have enough logarithmic separation. -/
theorem half_le_log_five_thirds : (1 / 2 : ℝ) ≤ Real.log (5 / 3) := by
  apply (Real.le_log_iff_exp_le (by norm_num)).mpr
  have hsq : Real.exp (1 / 2) ^ 2 < (5 / 3 : ℝ) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
    linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos (1 / 2)]

/-- Fixed logarithms in the circle bound, proved from the exponential series bound. -/
theorem backlund_circle_log_constants :
    Real.log 11 ≤ 3 ∧ Real.log 22 ≤ 4 ∧ Real.log 50 ≤ 4 := by
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 3
  have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 4
  rw [← Real.exp_nat_mul] at h3 h4
  norm_num at h3 h4
  exact ⟨(Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith),
    (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith),
    (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith)⟩

/-- The paired logarithmic mean grows by only `3/2 log T`. -/
theorem backlundCircleLogBound_le {T : ℝ} (hT : 10 ≤ T) :
    backlundCircleLogBound T ≤ 3 / 2 * Real.log T + 4 := by
  obtain ⟨_, h22, h50⟩ := backlund_circle_log_constants
  unfold backlundCircleLogBound
  rw [abs_of_nonneg (by linarith : 0 ≤ T), Real.log_mul (by norm_num) (by linarith : T ≠ 0),
    Real.log_mul (by norm_num) (pow_ne_zero 2 (by linarith : T ≠ 0)), Real.log_pow]
  linarith

/-- The real zeta factor at the fixed centre is at most eleven. -/
theorem norm_riemannZeta_eleven_tenths_le : ‖riemannZeta (11 / 10 : ℂ)‖ ≤ 11 := by
  have h := norm_riemannZeta_real_le_pole_add_one (by norm_num : (1 : ℝ) < 11 / 10)
  norm_num at h
  exact h

/-- The centre's Euler lower bound removes one logarithmic height factor. -/
theorem log_backlund_unit_centre_lower {T : ℝ} (hT : 10 ≤ T) :
    Real.log T - 3 ≤ Real.log ‖Backlund.zetaSurrogate ((11 / 10 : ℂ) + T * I)‖ := by
  have ht : 0 < T := by linarith
  have hZ : 0 < ‖riemannZeta (11 / 10 : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  have hc := abs_height_div_zeta_le_backlundSurrogate (by norm_num : (1 : ℝ) < 11 / 10) T
  norm_num only [ofReal_div, ofReal_ofNat] at hc
  rw [abs_of_pos ht] at hc
  have hlow : T / 11 ≤ ‖Backlund.zetaSurrogate ((11 / 10 : ℂ) + T * I)‖ :=
    (div_le_div_of_nonneg_left ht.le hZ norm_riemannZeta_eleven_tenths_le).trans hc
  have h := Real.log_le_log (by positivity : 0 < T / 11) hlow
  rw [Real.log_div ht.ne' (by norm_num)] at h
  linarith [backlund_circle_log_constants.1]

/-- After centre normalization, the averaged Jensen contribution is at most `log T + 14`. -/
theorem backlund_circle_normalized_mean_le {T : ℝ} (hT : 10 ≤ T) :
    (backlundCircleLogBound T -
      Real.log ‖Backlund.zetaSurrogate ((11 / 10 : ℂ) + T * I)‖) /
        Real.log (5 / 3) ≤ Real.log T + 14 := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hnum := backlundCircleLogBound_le hT
  have hc := log_backlund_unit_centre_lower hT
  have hden := half_le_log_five_thirds
  calc
    _ ≤ (Real.log T / 2 + 7) / Real.log (5 / 3) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ ≤ (Real.log T / 2 + 7) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by ring

end

end PrimeFactorUnimodality
