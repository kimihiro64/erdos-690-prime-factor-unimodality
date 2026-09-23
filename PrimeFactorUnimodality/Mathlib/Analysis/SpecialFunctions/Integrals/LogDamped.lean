/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedTail

/-! # Integrability of logarithmically weighted damped powers

The inverse-square comparison gives integrable majorants both for the
logarithmic density and for its reciprocal-height correction. An elementary
primitive proves integrability of `log(t)/t^2` without asymptotic constants.
-/

namespace Real

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- The elementary logarithmic inverse-square majorant is integrable above one. -/
theorem integrableOn_log_div_sq {u : ℝ} (hu : 1 < u) :
    IntegrableOn (fun t : ℝ => log t / t ^ 2) (Ioi u) := by
  have hd (t : ℝ) (ht : t ∈ Ici u) :
      HasDerivAt (fun t : ℝ => -(log t + 1) / t) (log t / t ^ 2) t := by
    have ht0 : t ≠ 0 := (lt_trans zero_lt_one (hu.trans_le ht)).ne'
    convert (((hasDerivAt_log ht0).add_const 1).neg.div (hasDerivAt_id t) ht0) using 1
    · funext t
      rfl
    · dsimp
      field_simp
      ring
  have hlog : Tendsto (fun t : ℝ => log t / t) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlim : Tendsto (fun t : ℝ => -(log t + 1) / t) atTop (𝓝 0) := by
    convert (hlog.add tendsto_inv_atTop_zero).neg using 1
    · funext t
      simp only [neg_div, add_div, one_div]
    · simp
  exact integrableOn_Ioi_deriv_of_nonneg' hd
    (fun t ht => div_nonneg (log_pos (hu.trans ht)).le (sq_nonneg t)) hlim

/-- Damped powers with exponent at least two are integrable on any tail above one. -/
theorem integrableOn_logDampedPower {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    IntegrableOn (logDampedPower a q) (Ioi u) := by
  have hc := continuousOn_logDampedPower (a := a) (q := q) (fun t (ht : t ∈ Ioi u) => hu.trans ht)
  apply (integrableOn_inv_sq_Ioi (lt_trans zero_lt_one hu)).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (logDampedPower_pos a q t)]
  simpa only [one_div, inv_pow] using logDampedPower_le_inv_sq ha hq (hu.trans ht)

/-- A logarithmic factor preserves integrability of the damped tail. -/
theorem integrableOn_log_mul_logDampedPower {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    IntegrableOn (fun t => log t * logDampedPower a q t) (Ioi u) := by
  have hc := continuousOn_logDampedPower (a := a) (q := q) (fun t (ht : t ∈ Ioi u) => hu.trans ht)
  have hl : ContinuousOn log (Ioi u) := continuousOn_id.log
    (fun _ ht => (lt_trans zero_lt_one (hu.trans ht)).ne')
  apply (integrableOn_log_div_sq hu).mono'
    ((hl.mul hc).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 := hu.trans ht
  change ‖log t * logDampedPower a q t‖ ≤ log t / t ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (log_pos ht1).le (logDampedPower_pos a q t).le)]
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (logDampedPower_le_inv_sq ha hq ht1) (log_pos ht1).le

/-- Division by height preserves integrability on a tail above one. -/
theorem integrableOn_logDampedPower_div {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    IntegrableOn (fun t => logDampedPower a q t / t) (Ioi u) := by
  have hc := continuousOn_logDampedPower (a := a) (q := q) (fun t (ht : t ∈ Ioi u) => hu.trans ht)
  have hd : ContinuousOn (fun t => logDampedPower a q t / t) (Ioi u) :=
    hc.div continuousOn_id (fun _ ht => (lt_trans zero_lt_one (hu.trans ht)).ne')
  apply (integrableOn_logDampedPower ha hq hu).mono'
    (hd.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (logDampedPower_pos a q t).le (lt_trans zero_lt_one (hu.trans ht)).le)]
  exact div_le_self (logDampedPower_pos a q t).le (hu.trans ht).le

/-- Any positive logarithm scale is allowed in the weighted density. -/
theorem integrableOn_log_div_mul_logDampedPower {a q u b : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) (hb : 0 < b) :
    IntegrableOn (fun t => log (t / b) * logDampedPower a q t) (Ioi u) := by
  apply ((integrableOn_log_mul_logDampedPower ha hq hu).sub
    ((integrableOn_logDampedPower ha hq hu).const_mul (log b))).congr_fun
      _ measurableSet_Ioi
  intro t ht
  simp only [Pi.sub_apply, log_div (lt_trans zero_lt_one (hu.trans ht)).ne' hb.ne', sub_mul]

end

end Real
