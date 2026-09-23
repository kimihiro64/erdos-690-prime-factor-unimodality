/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Unit-interval integrals of shifted logarithmic singularities

The exact primitive remains valid when the singularity lies inside the interval.
The elementary entropy inequality gives a uniform lower bound near that interval.
-/

namespace Real

open MeasureTheory

/-- The absolute-value logarithm at a shifted real zero is locally integrable. -/
theorem intervalIntegrable_log_abs_sub (u a b : ℝ) :
    IntervalIntegrable (fun x => log |x - u|) volume a b := by
  simpa only [log_abs, sub_add_cancel] using
    (intervalIntegral.intervalIntegrable_log' (a := a - u) (b := b - u)).comp_sub_right u

/-- The exact unit-interval integral, including singularities and both endpoints. -/
theorem integral_log_abs_sub (u : ℝ) :
    (∫ x in (0 : ℝ)..1, log |x - u|) =
      (1 - u) * log (1 - u) + u * log u - 1 := by
  simp_rw [log_abs]
  rw [intervalIntegral.integral_comp_sub_right log u, integral_log]
  simp only [zero_sub]
  ring_nf
  rw [log_neg_eq_log]

/-- A uniform lower bound for a logarithmic singularity within unit distance of zero. -/
theorem neg_two_le_integral_log_abs_sub {u : ℝ} (hu : |u| ≤ 1) :
    -2 ≤ ∫ x in (0 : ℝ)..1, log |x - u| := by
  rw [integral_log_abs_sub]
  by_cases hu0 : 0 ≤ u
  · have h1 := self_sub_one_le_mul_log hu0
    have h2 := self_sub_one_le_mul_log (by linarith [(abs_le.mp hu).2] : 0 ≤ 1 - u)
    linarith
  · have hulog : log u ≤ 0 := by
      rw [← log_abs]
      exact log_nonpos (abs_nonneg u) hu
    have h1 := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hu0) hulog
    have h2 := mul_log_nonneg (by linarith : 1 ≤ 1 - u)
    linarith

end Real
