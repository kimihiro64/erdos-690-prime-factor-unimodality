/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic

/-! # Entire dependence of a finite Laplace transform on its parameter

Differentiation under the finite integral is justified by an explicit
locally uniform exponential majorant. The source is only required to be
continuous on its integration interval; endpoint vanishing is unnecessary.
-/

namespace Complex

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- Differentiating in the complex parameter multiplies the source by `-t`. -/
theorem hasDerivAt_finiteLaplace {f : ℝ → ℂ} {d : ℝ}
    (hf : ContinuousOn f (uIcc 0 d)) (s : ℂ) :
    HasDerivAt (finiteLaplace f d) (finiteLaplace (fun t => -(t : ℂ) * f t) d s) s := by
  let F' : ℂ → ℝ → ℂ := fun w t => exp (-w * (t : ℂ)) * (-(t : ℂ) * f t)
  have hsource : ContinuousOn (fun t : ℝ => -(t : ℂ) * f t) (uIcc 0 d) :=
    continuous_ofReal.neg.continuousOn.mul hf
  have hF' (w : ℂ) : IntervalIntegrable (F' w) volume 0 d :=
    intervalIntegrable_finiteLaplace hsource w
  have hbc : Continuous (fun t : ℝ => |t| * Real.exp ((‖s‖ + 1) * |t|)) := by fun_prop
  have hb : IntervalIntegrable
      (fun t : ℝ => |t| * Real.exp ((‖s‖ + 1) * |t|) * ‖f t‖) volume 0 d :=
    (hbc.continuousOn.mul hf.norm).intervalIntegrable
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t => exp (-w * (t : ℂ)) * f t) (F' := F')
    (s := Metric.ball s 1) (x₀ := s) (bound := fun t : ℝ =>
      |t| * Real.exp ((‖s‖ + 1) * |t|) * ‖f t‖)
    (Metric.ball_mem_nhds s (by norm_num))
    (Filter.Eventually.of_forall fun w =>
      (intervalIntegrable_iff.mp (intervalIntegrable_finiteLaplace hf w)).aestronglyMeasurable)
    (intervalIntegrable_finiteLaplace hf s)
    (intervalIntegrable_iff.mp (hF' s)).aestronglyMeasurable ?_ hb ?_
  · exact h.2
  · filter_upwards with t _
    intro w hw
    have hw' : ‖w‖ ≤ ‖s‖ + 1 := by
      have ht := norm_le_norm_sub_add w s
      have hd : ‖w - s‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
      linarith
    have he : (-w * (t : ℂ)).re ≤ (‖s‖ + 1) * |t| := by
      calc
        _ ≤ ‖-w * (t : ℂ)‖ := re_le_norm _
        _ = ‖w‖ * |t| := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hw' (abs_nonneg _)
    calc
      ‖F' w t‖ = |t| * Real.exp ((-w * (t : ℂ)).re) * ‖f t‖ := by
        simp [F', norm_exp, mul_assoc, mul_comm, mul_left_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (abs_nonneg _)) (norm_nonneg _)
  · filter_upwards with t _
    intro w _
    simpa [F', mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp.mul_const (f t))

/-- A continuous source on a finite interval has an entire Laplace transform. -/
theorem differentiable_finiteLaplace {f : ℝ → ℂ} {d : ℝ}
    (hf : ContinuousOn f (uIcc 0 d)) : Differentiable ℂ (finiteLaplace f d) :=
  fun s => (hasDerivAt_finiteLaplace hf s).differentiableAt

end

end Complex
