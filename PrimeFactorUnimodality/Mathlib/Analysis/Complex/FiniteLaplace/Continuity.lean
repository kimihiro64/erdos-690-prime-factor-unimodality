/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic

/-! # Continuity of finite Laplace transforms on vertical lines

Dominated convergence on the finite source interval gives continuity in
height. The source needs continuity only on that interval, not across the
origin after extension by zero. No sign restriction is imposed on the line.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- Continuity in height, with a dominating function independent of height. -/
theorem continuous_finiteLaplace_vertical {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (s : ℂ) :
    Continuous (fun t : ℝ => finiteLaplace f d (s - (t : ℂ) * I)) := by
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun u : ℝ => Real.exp (-s.re * u) * ‖f u‖)
  · intro t
    simpa only [uIoc_of_le hd] using
      (intervalIntegrable_finiteLaplace hf' (s - (t : ℂ) * I)).1.aestronglyMeasurable
  · intro t
    filter_upwards with u _
    simp [norm_exp]
  · exact ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-s.re * u))).continuousOn.mul
      hf'.norm).intervalIntegrable
  · filter_upwards with u _
    fun_prop

end

end Complex
