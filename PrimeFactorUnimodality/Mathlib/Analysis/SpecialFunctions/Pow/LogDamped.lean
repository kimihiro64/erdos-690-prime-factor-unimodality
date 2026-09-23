/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Powers with inverse-logarithmic exponential damping

The derivative keeps the sign-changing factor explicit. The square-root
bound controls the global maximum, while derivative signs give monotonicity
on any convex domain above one. Parameters are arbitrary reals, not tied
to a particular counting problem or a supplied zero-free region.
-/

namespace Real

noncomputable section

/-- A real power with an exponential factor inversely proportional to its logarithm. -/
def logDampedPower (a q t : ℝ) : ℝ := exp (-q * log t - a / log t)

/-- The exponential definition agrees with the product of the two conventional factors. -/
theorem logDampedPower_eq_rpow_mul {a q t : ℝ} (ht : 0 < t) :
    logDampedPower a q t = t ^ (-q) * exp (-a / log t) := by
  rw [logDampedPower, Real.rpow_def_of_pos ht, ← Real.exp_add]
  congr 1
  ring

/-- The derivative exhibits the turning-point factor without differentiating a variable power. -/
theorem hasDerivAt_logDampedPower {a q t : ℝ} (ht : 1 < t) :
    HasDerivAt (logDampedPower a q)
      (logDampedPower a q t * (a - q * log t ^ 2) / (t * log t ^ 2)) t := by
  have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  have hlog : log t ≠ 0 := (log_pos ht).ne'
  have hd := (((hasDerivAt_log ht0).const_mul (-q)).sub
    ((hasDerivAt_const t a).div (hasDerivAt_log ht0) hlog)).exp
  apply hd.congr_deriv
  dsimp [logDampedPower]
  field_simp
  ring

/-- Increasing the damping parameter decreases the kernel at every height above one. -/
theorem logDampedPower_antitone_parameter {a b q t : ℝ} (hab : a ≤ b) (ht : 1 < t) :
    logDampedPower b q t ≤ logDampedPower a q t := by
  unfold logDampedPower
  apply Real.exp_le_exp.mpr
  have hd := div_le_div_of_nonneg_right hab (Real.log_pos ht).le
  linarith only [hd]


/-- An arithmetic-geometric mean bound controls the kernel uniformly above one. -/
theorem logDampedPower_le_exp_sqrt {a q t : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (ht : 1 < t) :
    logDampedPower a q t ≤ exp (-2 * sqrt (a * q)) := by
  have hL : 0 < log t := log_pos ht
  have hs : 0 ≤ q * log t + a / log t := by positivity
  have hsq := sq_sqrt (mul_nonneg ha hq)
  have hId : (q * log t + a / log t) ^ 2 - 4 * (a * q) =
      (q * log t - a / log t) ^ 2 := by
    field_simp
    ring
  have hb : 2 * sqrt (a * q) ≤ q * log t + a / log t := by
    nlinarith [sq_nonneg (q * log t - a / log t), sqrt_nonneg (a * q)]
  unfold logDampedPower
  apply exp_le_exp.mpr
  linarith

/-- The kernel is increasing wherever its logarithmic derivative has nonnegative sign. -/
theorem logDampedPower_monotoneOn {a q : ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (ht : ∀ t ∈ D, 1 < t) (hreg : ∀ t ∈ D, q * log t ^ 2 ≤ a) :
    MonotoneOn (logDampedPower a q) D := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg hD
    (fun t htD => (hasDerivAt_logDampedPower (ht t htD)).continuousAt.continuousWithinAt)
    (fun t htD => (hasDerivAt_logDampedPower (ht t (interior_subset htD))).hasDerivWithinAt)
  intro t htD
  have htx : 0 < t := lt_trans zero_lt_one (ht t (interior_subset htD))
  exact div_nonneg (mul_nonneg (exp_pos _).le (sub_nonneg.mpr (hreg t (interior_subset htD))))
    (mul_nonneg htx.le (sq_nonneg _))

/-- The kernel is decreasing wherever its logarithmic derivative has nonpositive sign. -/
theorem logDampedPower_antitoneOn {a q : ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (ht : ∀ t ∈ D, 1 < t) (hreg : ∀ t ∈ D, a ≤ q * log t ^ 2) :
    AntitoneOn (logDampedPower a q) D := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos hD
    (fun t htD => (hasDerivAt_logDampedPower (ht t htD)).continuousAt.continuousWithinAt)
    (fun t htD => (hasDerivAt_logDampedPower (ht t (interior_subset htD))).hasDerivWithinAt)
  intro t htD
  have htx : 0 < t := lt_trans zero_lt_one (ht t (interior_subset htD))
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (sub_nonpos.mpr (hreg t (interior_subset htD))))
    (mul_nonneg htx.le (sq_nonneg _))

end

end Real
