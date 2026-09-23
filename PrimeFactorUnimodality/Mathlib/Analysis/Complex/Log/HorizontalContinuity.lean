/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.Basic
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogShift

/-! # Continuity of horizontal logarithmic-distance integrals through zeros

The only exceptional real coordinate is the real part of the fixed zero.
Away from that singleton, the distance is bounded below by the horizontal
distance. Its integrable logarithmic singularity dominates the negative
part uniformly in height; a compact bound controls the positive part.
Dominated convergence therefore applies even when the moving line meets
the zero, including at an integration endpoint.
-/

namespace Complex

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

private theorem horizontal_distance_ne_zero {w : ℂ} {x t : ℝ} (hx : x ≠ w.re) :
    (x : ℂ) + t * I - w ≠ 0 := by
  intro he
  apply hx
  have hr := congrArg Complex.re he
  simpa using sub_eq_zero.mp (by simpa using hr : x - w.re = 0)

/-- A shifted horizontal logarithmic distance is integrable at every height, including singular ones. -/
theorem intervalIntegrable_log_norm_horizontal_sub (w : ℂ) (t a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖(x : ℂ) + t * I - w‖) volume a b := by
  have he (x : ℝ) : (x : ℂ) + t * I - w = (x : ℂ) - (w - t * I) := by ring
  simp_rw [he]
  exact intervalIntegrable_log_norm_real_sub (w - t * I) a b

/-- Integrating a logarithmic distance across a bounded segment is continuous through zero heights. -/
theorem continuous_integral_log_norm_horizontal_sub (w : ℂ) (a b : ℝ) :
    Continuous (fun t : ℝ => ∫ x in a..b, Real.log ‖(x : ℂ) + t * I - w‖) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  let M : ℝ := |a| + |b| + |T| + 1 + ‖w‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun x : ℝ => |Real.log (|x - w.re|)| + M)
  · exact Filter.Eventually.of_forall (fun t =>
      (intervalIntegrable_iff.mp (intervalIntegrable_log_norm_horizontal_sub w t a b)).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds T (by norm_num : (0 : ℝ) < 1)] with t ht
    filter_upwards [volume.ae_ne w.re] with x hx hxab
    have hnorm : 0 < ‖(x : ℂ) + t * I - w‖ := norm_pos_iff.mpr (horizontal_distance_ne_zero hx)
    have hlow : Real.log |x - w.re| ≤ Real.log ‖(x : ℂ) + t * I - w‖ :=
      Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hx))
        (by simpa using abs_re_le_norm ((x : ℂ) + t * I - w))
    have hx' := uIoc_subset_uIcc hxab
    have hxabs : |x| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor
      · exact (le_min (by linarith [neg_abs_le a, abs_nonneg b])
          (by linarith [neg_abs_le b, abs_nonneg a])).trans hx'.1
      · exact hx'.2.trans (max_le (by linarith [le_abs_self a, abs_nonneg b])
          (by linarith [le_abs_self b, abs_nonneg a]))
    have htabs : |t| ≤ |T| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      exact abs_le.mpr ⟨by linarith [neg_abs_le T], by linarith [le_abs_self T]⟩
    have hnup : ‖(x : ℂ) + t * I - w‖ ≤ M := by
      have hn := norm_sub_le ((x : ℂ) + t * I) w
      have ha := norm_add_le (x : ℂ) (t * I)
      simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one] at ha
      dsimp [M]
      linarith
    have hlogup := (Real.log_le_sub_one_of_pos hnorm).trans (by linarith :
      ‖(x : ℂ) + t * I - w‖ - 1 ≤ M)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le (Real.log |x - w.re|), abs_nonneg (Real.log |x - w.re|)]
  · exact (Real.intervalIntegrable_log_abs_sub w.re a b).abs.add intervalIntegrable_const
  · filter_upwards [volume.ae_ne w.re] with x hx _
    exact (show ContinuousAt (fun t : ℝ => (x : ℂ) + t * I - w) T by fun_prop).norm.log
      (norm_ne_zero_iff.mpr (horizontal_distance_ne_zero hx))

end

end Complex
