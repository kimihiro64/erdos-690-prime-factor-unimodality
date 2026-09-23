import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalShift
import PrimeFactorUnimodality.Helpers.Analytic.TuringZetaLogStep

/-! # An explicit lower bound for the complete horizontal zeta log integral

The actual xi log-ratio identity and complete spectral estimate control
the shifted zeta decrement. The pole is nonnegative and Gamma loses at
most two; the two right-hand tails lose at most four more. This proves a
coarse logarithmic lower bound without numerical zero information.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

private theorem zeta_decrement_translate (T x : ℝ) :
    turingZetaLogDecrement T x =
      Real.log ‖riemannZeta (((x + 1 / 2 : ℝ) : ℂ) + T * I)‖ -
        Real.log ‖riemannZeta (((x + 1 / 2 + 1 : ℝ) : ℂ) + T * I)‖ := by
  unfold turingZetaLogDecrement
  have h0 : (x : ℂ) + ((1 / 2 : ℂ) + T * I) =
      ((x + 1 / 2 : ℝ) : ℂ) + T * I := by push_cast; ring
  have h1 : (x : ℂ) + ((1 / 2 : ℂ) + T * I) + 1 =
      ((x + 1 / 2 + 1 : ℝ) : ℂ) + T * I := by push_cast; ring
  rw [h1, h0]

/-- The normalized zeta decrement is integrable at every nonzero height. -/
theorem intervalIntegrable_turingZetaLogDecrement {T : ℝ} (hT : T ≠ 0) :
    IntervalIntegrable (turingZetaLogDecrement T) volume 0 1 := by
  let F := fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖
  have h0 : IntervalIntegrable (fun x => F (x + 1 / 2)) volume 0 1 :=
    (IntervalIntegrable.comp_add_right_iff (f := F) (c := 1 / 2)).mpr
      (intervalIntegrable_log_norm_riemannZeta_horizontal hT _ _)
  have h1 : IntervalIntegrable (fun x => F (x + 1 / 2 + 1)) volume 0 1 := by
    have h : IntervalIntegrable (fun x => F (x + (1 / 2 + 1))) volume 0 1 :=
      (IntervalIntegrable.comp_add_right_iff (f := F) (c := 1 / 2 + 1)).mpr
        (intervalIntegrable_log_norm_riemannZeta_horizontal hT _ _)
    simpa only [add_assoc] using h
  simpa only [funext (zeta_decrement_translate T)] using h0.sub h1

/-- Translation relates the normalized decrement to the actual shifted integral. -/
theorem integral_turingZetaLogDecrement (T : ℝ) :
    (∫ x in (0 : ℝ)..1, turingZetaLogDecrement T x) = turingShiftedLogIntegral 1 T := by
  simp_rw [zeta_decrement_translate]
  have h := intervalIntegral.integral_comp_add_right
    (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ -
      Real.log ‖riemannZeta (((x + 1 : ℝ) : ℂ) + T * I)‖)
    (a := 0) (b := 1) (1 / 2)
  simpa only [zero_add, turingShiftedLogIntegral, add_comm (1 : ℝ) (1 / 2)] using h

/-- The actual shifted zeta integral is bounded below by the complete xi budget and two. -/
theorem turingShiftedLogIntegral_one_ge {T : ℝ} (hT : T ≠ 0) :
    -(8 * Real.log (|T| / 2 + 3) + 90) ≤ turingShiftedLogIntegral 1 T := by
  have hi := intervalIntegrable_turingXiLogIncrement T
  have hz := intervalIntegrable_turingZetaLogDecrement hT
  have h := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
    (hi.neg.sub intervalIntegrable_const) hz (f := fun x => -turingXiLogIncrement T x - 2) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (ae_riemannXi_horizontal_ne_zero (1 / 2) T)] with x hx hxi
      apply turingZetaLogDecrement_ge hT hx.1
      simpa only [ofReal_div, ofReal_one, ofReal_ofNat, add_assoc] using hxi)
  have hsub := intervalIntegral.integral_sub
    (f := fun x => -turingXiLogIncrement T x) (g := fun _ => (2 : ℝ))
    hi.neg intervalIntegrable_const
  rw [hsub,
    intervalIntegral.integral_neg, intervalIntegral.integral_const,
    integral_turingZetaLogDecrement] at h
  simp only [sub_zero, one_smul] at h
  linarith [integral_turingXiLogIncrement_le T]

/-- The full infinite horizontal zeta log integral has an explicit logarithmic lower bound. -/
theorem turingHorizontalIntegral_ge {T : ℝ} (hT : T ≠ 0) :
    -(8 * Real.log (|T| / 2 + 3) + 94) ≤ turingHorizontalIntegral T := by
  have hs := turingShiftedLogIntegral_one_ge hT
  have ht := turingShiftedLogIntegral_one_sub_four_le hT
  linarith

end

end PrimeFactorUnimodality
