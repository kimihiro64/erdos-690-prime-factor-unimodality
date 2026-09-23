import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalLog

/-! # Exact shift decomposition of the horizontal logarithmic integral

Trudgian, arXiv:0903.1885, equation (2.8), separates a shifted logarithmic
difference from two right-half-plane integrals. Writing the difference
of real log moduli avoids imposing nonvanishing at every point of a
segment. The two remaining integrals have proved absolute budgets.
At shift one their combined possible loss is at most four. The spectral
lower bound for the shifted difference is still required.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The finite logarithmic difference before and after shifting to the right. -/
def turingShiftedLogIntegral (d T : ℝ) : ℝ :=
  ∫ x in (1 / 2 : ℝ)..(1 / 2 + d),
    Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ -
      Real.log ‖riemannZeta (((x + d : ℝ) : ℂ) + T * I)‖

/-- The exact shift decomposition retains both right-half-plane integrals. -/
theorem turingHorizontalIntegral_eq_shift {T d : ℝ} (hT : T ≠ 0) (hd : 1 / 2 < d) :
    turingHorizontalIntegral T = turingShiftedLogIntegral d T +
      (∫ x in Ioi (1 / 2 + d), Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) +
      ∫ x in (1 / 2 + d)..(1 / 2 + d + d),
        Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ := by
  have hfirst := intervalIntegrable_log_norm_riemannZeta_horizontal hT (1 / 2) (1 / 2 + d)
  have hsecond : IntervalIntegrable
      (fun x : ℝ => Real.log ‖riemannZeta (((x + d : ℝ) : ℂ) + T * I)‖)
      volume (1 / 2) (1 / 2 + d) :=
    (IntervalIntegrable.comp_add_right_iff
      (f := fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) (c := d)).mpr
      (intervalIntegrable_log_norm_riemannZeta_horizontal hT (1 / 2 + d) (1 / 2 + d + d))
  have htranslate := intervalIntegral.integral_comp_add_right
    (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖)
    (a := 1 / 2) (b := 1 / 2 + d) d
  rw [turingHorizontalIntegral_eq_split hT (by linarith : 1 < 1 / 2 + d),
    turingShiftedLogIntegral, intervalIntegral.integral_sub hfirst hsecond, htranslate]
  ring

/-- Only the shifted integral remains after explicitly bounding both right-hand contributions. -/
theorem turingShiftedLogIntegral_sub_budget_le {T d : ℝ} (hT : T ≠ 0) (hd : 1 / 2 < d) :
    turingShiftedLogIntegral d T -
        2 * (Real.log ‖riemannZeta ((1 / 2 + d : ℝ) : ℂ)‖ / Real.log 2) ≤
      turingHorizontalIntegral T := by
  have hc : 1 < 1 / 2 + d := by linarith
  have ht := (abs_le.mp (abs_integral_log_norm_riemannZeta_horizontal_Ioi_le hc T)).1
  have hm := (abs_le.mp (abs_integral_log_norm_riemannZeta_horizontal_le hc
    (by linarith : 1 / 2 + d ≤ 1 / 2 + d + d) T)).1
  rw [turingHorizontalIntegral_eq_shift hT hd]
  linarith

/-- A unit shift incurs at most four units from the two complete right-half-plane budgets. -/
theorem turingShiftedLogIntegral_one_sub_four_le {T : ℝ} (hT : T ≠ 0) :
    turingShiftedLogIntegral 1 T - 4 ≤ turingHorizontalIntegral T := by
  have hz : ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ ≤ 4 := by
    have h := norm_riemannZeta_real_le_pole_add_one (by norm_num : (1 : ℝ) < 3 / 2)
    norm_num at h ⊢
    linarith
  have hp : 0 < ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  have hl := Real.log_le_log hp hz
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow] at hl
  have hb : Real.log ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ / Real.log 2 ≤ 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num))).mpr hl
  have h := turingShiftedLogIntegral_sub_budget_le hT (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at h hb
  linarith

end

end PrimeFactorUnimodality
