/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.Basic
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogShift

/-! # A bounded logarithmic step near the real axis

The denominator is compared with its real part almost everywhere, excluding
the single real singularity. The shifted numerator is bounded away from zero.
-/

namespace Complex

open MeasureTheory Set

private theorem log_norm_shift_le_two {w : ℂ} (hw : |w.re| ≤ 1 / 2)
    (hv : |w.im| ≤ 1) {x : ℝ} (hx : x ∈ Icc 0 1) :
    Real.log ‖((x + 1 : ℝ) : ℂ) - w‖ ≤ 2 := by
  have hr := abs_le.mp hw
  have hnorm := norm_le_abs_re_add_abs_im (((x + 1 : ℝ) : ℂ) - w)
  have hreal := abs_re_le_norm (((x + 1 : ℝ) : ℂ) - w)
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, abs_neg] at hnorm hreal
  rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x + 1 - w.re)] at hnorm hreal
  have hpos : 0 < ‖((x + 1 : ℝ) : ℂ) - w‖ := by linarith [hx.1]
  have hlog := Real.log_le_log hpos (show ‖((x + 1 : ℝ) : ℂ) - w‖ ≤ 4 by
    linarith [hx.2])
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hfour := Real.log_pow (2 : ℝ) 2
  norm_num at htwo hfour
  linarith

/-- Each unit logarithmic step has integral at most four in the half-unit strip at low height. -/
theorem logNormStepIntegral_le_four {w : ℂ} (hw : |w.re| ≤ 1 / 2)
    (hv : |w.im| ≤ 1) : logNormStepIntegral w ≤ 4 := by
  have hr := Real.intervalIntegrable_log_abs_sub w.re 0 1
  have hcomp := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_logNormStep w 0 1) (intervalIntegrable_const.sub hr) (g :=
      fun x => 2 - Real.log |x - w.re|) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae (volume.ae_ne w.re)] with x hx hne
        have hden : Real.log |x - w.re| ≤ Real.log ‖(x : ℂ) - w‖ :=
          Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hne))
            (by simpa only [sub_re, ofReal_re] using abs_re_le_norm ((x : ℂ) - w))
        have hnum := log_norm_shift_le_two hw hv hx
        dsimp only [logNormStep]
        linarith only [hden, hnum])
  rw [intervalIntegral.integral_sub intervalIntegrable_const hr,
    intervalIntegral.integral_const] at hcomp
  have hlower := Real.neg_two_le_integral_log_abs_sub (hw.trans (by norm_num))
  change logNormStepIntegral w ≤ _ at hcomp
  simp only [sub_zero, one_smul] at hcomp
  linarith

end Complex
