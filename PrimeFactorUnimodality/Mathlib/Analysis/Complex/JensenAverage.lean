/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Jonas Whidden
-/
import Mathlib.Analysis.Complex.JensenFormula

/-! # Jensen's zero-mass estimate retaining the circle average

This factors the divisor comparison from Mathlib's
`AnalyticOnNhd.sum_divisor_le` without replacing the logarithmic circle
average by a supremum. The comparison proof is adapted from Stefan
Kebekus's Apache-2.0 `Mathlib/Analysis/Complex/JensenFormula.lean`.
The pinned Mathlib revision is `5ed2965256430c3649e86755f9576b54eca72435`.
The existing Jensen identity supplies the complete analytic input.
-/

open Complex Metric Real Set MeromorphicOn

/-- The inner zero mass is bounded by the actual outer logarithmic average. -/
theorem AnalyticOnNhd.sum_divisor_le_circleAverage {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0) :
    ((∑ᶠ u, divisor f (closedBall c r) u : ℤ) : ℝ) ≤
      (circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have ha : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa only [abs_of_pos hR] using hf
  trans ∑ᶠ u, (divisor f (closedBall c r) u : ℝ)
  · exact (map_finsum (Int.castRingHom ℝ) ((divisor f (closedBall c r)).finiteSupport
      (isCompact_closedBall ..))).le
  apply (le_div_iff₀ (Real.log_pos ((one_lt_div hr).mpr hrR))).mpr
  rw [finsum_mul]
  have hj := ha.circleAverage_log_norm hR.ne' hc
  rw [abs_of_pos hR] at hj
  rw [hj, add_sub_cancel_right]
  refine finsum_le_finsum ?_ ?_ fun u => ?_
  · exact ((divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..)).subset
      fun _ _ => by simp_all
  · exact ((divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..)).subset
      fun _ _ => by simp_all
  · by_cases h1 : u ∈ closedBall c R
    · by_cases h2 : u ∈ closedBall c r
      · simp only [AnalyticOnNhd.divisor_apply, hf,
          hf.mono (closedBall_subset_closedBall hrR.le), h1, h2]
        by_cases h3 : u = c
        · rw [h3, (hf c (mem_closedBall_self hR.le)).analyticOrderAt_eq_zero.mpr hc]
          simp
        gcongr 2
        · simp
        · have hu : ‖c - u‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm'] using h2
          simpa only [div_eq_mul_inv] using
            div_le_div_of_nonneg_left hR.le (norm_pos_iff.mpr
              (sub_ne_zero.mpr (Ne.symm h3))) hu
      · simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
          Int.cast_zero, zero_mul]
        apply mul_nonneg (mod_cast hf.divisor_nonneg u) (Real.log_nonneg ?_)
        have hu : ‖c - u‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm'] using h1
        have hn : 0 < ‖c - u‖ := by
          have : r < ‖c - u‖ := by simpa only [mem_closedBall, dist_eq_norm', not_le] using h2
          exact hr.trans this
        simpa only [div_eq_mul_inv] using (one_le_div hn).mpr hu
    · have h2 : u ∉ closedBall c r := fun hu => h1 (closedBall_subset_closedBall hrR.le hu)
      simp [h1, h2]
