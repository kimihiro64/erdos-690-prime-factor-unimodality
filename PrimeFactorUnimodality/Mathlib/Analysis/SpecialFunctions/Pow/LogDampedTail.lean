/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedShape

/-! # Decay and monotonicity of damped-power tails

An inverse-square comparison controls convergence for exponents at least
two. Beyond the exact turning height the kernel is decreasing, so it can
be used in infinite summation by parts without an assumed boundary limit.
-/

namespace Real

open Filter Set
open scoped Topology

/-- Nonnegative damping never enlarges the undamped power. -/
theorem logDampedPower_le_rpow {a q t : ℝ} (ha : 0 ≤ a) (ht : 1 < t) :
    logDampedPower a q t ≤ t ^ (-q) := by
  rw [logDampedPower_eq_rpow_mul (lt_trans zero_lt_one ht)]
  apply mul_le_of_le_one_right (rpow_nonneg (lt_trans zero_lt_one ht).le _)
  exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
    (log_pos ht).le)

/-- Exponents at least two admit the summable inverse-square majorant. -/
theorem logDampedPower_le_inv_sq {a q t : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (ht : 1 < t) :
    logDampedPower a q t ≤ 1 / t ^ 2 := by
  refine (logDampedPower_le_rpow ha ht).trans ?_
  have he : t ^ (-q) ≤ t ^ (-(2 : ℝ)) :=
    rpow_le_rpow_of_exponent_le ht.le (neg_le_neg hq)
  simpa only [rpow_neg (lt_trans zero_lt_one ht).le, rpow_two, one_div] using he

/-- The damped kernel vanishes at infinity for exponents at least two. -/
theorem tendsto_logDampedPower_atTop {a q : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) :
    Tendsto (logDampedPower a q) atTop (𝓝 0) := by
  have hz : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by decide : 2 ≠ 0)] using
      (tendsto_inv_atTop_zero.pow 2 : Tendsto (fun t : ℝ => (t⁻¹) ^ 2) atTop (𝓝 (0 ^ 2)))
  apply squeeze_zero' (Eventually.of_forall (fun t => (logDampedPower_pos _ _ t).le)) _ hz
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  exact logDampedPower_le_inv_sq ha hq ht

/-- Beyond its turning point the kernel decreases on the entire open tail. -/
theorem antitoneOn_logDampedPower_after {a q u : ℝ} (ha : 0 ≤ a) (hq : 0 < q)
    (hu : 1 < u) (hw : exp (sqrt (a / q)) ≤ u) :
    AntitoneOn (logDampedPower a q) (Ioi u) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi u)
    (continuousOn_logDampedPower (fun t ht => hu.trans ht))
    (fun t ht => (hasDerivAt_logDampedPower (hu.trans (interior_subset ht))).hasDerivWithinAt)
  intro t ht
  exact logDampedPowerSlope_nonpos_after ha hq (hu.trans (interior_subset ht))
    (hw.trans (interior_subset ht).le)

end Real
