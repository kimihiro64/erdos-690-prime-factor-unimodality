/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedShape

/-! # Elementary bounds for finite damped logarithmic windows

The exponent-one kernel need not be integrable at infinity. On a finite
window, an elementary upper primitive bounds its logarithmic density.
This is the endpoint estimate used in the Rosser increasing branch.
-/

namespace Real

noncomputable section

open MeasureTheory Set

/-- An upper primitive for the exponent-one logarithmic density above its scale. -/
def logDampedWindowPrimitive (a b t : ℝ) : ℝ :=
  exp (-a / log t) * (log t ^ 2 / a) * (log t - log b)

/-- The upper primitive's derivative is the density plus an explicit correction. -/
theorem hasDerivAt_logDampedWindowPrimitive {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 1 < t) :
    HasDerivAt (logDampedWindowPrimitive a b)
      (log (t / b) * logDampedPower a 1 t +
        exp (-a / log t) / t * ((2 * log t * (log t - log b) + log t ^ 2) / a)) t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hL := log_pos ht
  have hd := ((((hasDerivAt_const t (-a)).div (hasDerivAt_log ht0.ne') hL.ne').exp.mul
    (((hasDerivAt_log ht0.ne').pow 2).div_const a)).mul
    ((hasDerivAt_log ht0.ne').sub_const (log b)))
  convert hd using 1
  · funext t
    rfl
  · dsimp
    rw [logDampedPower_eq_rpow_mul ht0, rpow_neg_one, log_div ht0.ne' hb.ne']
    field_simp [ha.ne', ht0.ne', hL.ne']
    ring

/-- The correction has the right sign throughout the window above the logarithm scale. -/
theorem logDampedWindow_correction_nonneg {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 1 < t) (hbt : b ≤ t) :
    0 ≤ exp (-a / log t) / t * ((2 * log t * (log t - log b) + log t ^ 2) / a) := by
  have hl : 0 ≤ log t := (log_pos ht).le
  have hm : 0 ≤ log t - log b := sub_nonneg.mpr (log_le_log hb hbt)
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  positivity

/-- The finite logarithmic density is bounded by the difference of its upper primitive. -/
theorem integral_logDampedPower_one_le_sub {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : 1 < u) (hbu : b ≤ u) (huv : u ≤ v) :
    (∫ t in Icc u v, log (t / b) * logDampedPower a 1 t) ≤
      logDampedWindowPrimitive a b v - logDampedWindowPrimitive a b u := by
  have hpos (t : ℝ) (ht : t ∈ Icc u v) : 1 < t := hu.trans_le ht.1
  have hlog : ContinuousOn (fun t : ℝ => log (t / b)) (Icc u v) :=
    (continuousOn_id.div_const b).log (fun t ht =>
      (div_pos (lt_trans zero_lt_one (hpos t ht)) hb).ne')
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
  apply intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le huv
    (fun t ht => (hasDerivAt_logDampedWindowPrimitive ha hb
      (hpos t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_logDampedWindowPrimitive ha hb (hu.trans ht.1)).hasDerivWithinAt)
    (hlog.mul (continuousOn_logDampedPower hpos)).integrableOn_Icc
  intro t ht
  exact le_add_of_nonneg_right
    (logDampedWindow_correction_nonneg ha hb (hu.trans ht.1) (hbu.trans ht.1.le))

/-- The lower endpoint term is nonnegative and may be discarded. -/
theorem integral_logDampedPower_one_le_endpoint {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : 1 < u) (hbu : b ≤ u) (huv : u ≤ v) :
    (∫ t in Icc u v, log (t / b) * logDampedPower a 1 t) ≤
      logDampedWindowPrimitive a b v := by
  have hl : 0 ≤ log u - log b := sub_nonneg.mpr (log_le_log hb hbu)
  have hf : 0 ≤ logDampedWindowPrimitive a b u := by
    unfold logDampedWindowPrimitive
    positivity
  exact (integral_logDampedPower_one_le_sub ha hb hu hbu huv).trans (sub_le_self _ hf)

/-- Exponential cutoffs give the scalar expression used for the Rosser window parameter. -/
theorem logDampedWindowPrimitive_exp {X ν b : ℝ} (hX : 0 < X) (hν : 0 < ν) :
    logDampedWindowPrimitive (X ^ 2) b (exp (ν * X)) =
      exp (-X / ν) * ν ^ 2 * (ν * X - log b) := by
  unfold logDampedWindowPrimitive
  rw [log_exp]
  have he : -(X ^ 2) / (ν * X) = -X / ν := by
    field_simp
  have hf : (ν * X) ^ 2 / X ^ 2 = ν ^ 2 := by
    field_simp
  rw [he, hf]

end

end Real
