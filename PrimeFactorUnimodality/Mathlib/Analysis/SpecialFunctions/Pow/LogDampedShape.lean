/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDamped

/-! # The turning point of inverse-logarithmically damped powers

For positive exponent `q`, the derivative changes sign at
`exp(sqrt(a/q))`. The statements include the exact turning point and the
degenerate case `a=0`. Local continuity of the explicit slope supports
integration against counting functions without a differentiability premise.
-/

namespace Real

noncomputable section

/-- The explicit slope, including its sign-changing factor. -/
def logDampedPowerSlope (a q t : ℝ) : ℝ :=
  logDampedPower a q t * (a - q * log t ^ 2) / (t * log t ^ 2)

/-- The exponential kernel is strictly positive for every real parameter. -/
theorem logDampedPower_pos (a q t : ℝ) : 0 < logDampedPower a q t := exp_pos _

/-- The kernel is continuous on any domain above one. -/
theorem continuousOn_logDampedPower {a q : ℝ} {D : Set ℝ} (hD : ∀ t ∈ D, 1 < t) :
    ContinuousOn (logDampedPower a q) D :=
  fun t ht => (hasDerivAt_logDampedPower (hD t ht)).continuousAt.continuousWithinAt

/-- The explicit slope is continuous away from the logarithmic singularity. -/
theorem continuousOn_logDampedPowerSlope {a q : ℝ} {D : Set ℝ} (hD : ∀ t ∈ D, 1 < t) :
    ContinuousOn (logDampedPowerSlope a q) D := by
  have hlog : ContinuousOn log D := continuousOn_id.log
    (fun t ht => (lt_trans zero_lt_one (hD t ht)).ne')
  exact ((continuousOn_logDampedPower hD).mul
    (continuousOn_const.sub (continuousOn_const.mul (hlog.pow 2)))).div
    (continuousOn_id.mul (hlog.pow 2)) (fun t ht =>
      mul_ne_zero (lt_trans zero_lt_one (hD t ht)).ne' (pow_ne_zero _ (log_pos (hD t ht)).ne'))

/-- Before the turning point the explicit derivative is nonnegative. -/
theorem logDampedPowerSlope_nonneg_before {a q t : ℝ}
    (ha : 0 ≤ a) (hq : 0 < q) (ht : 1 < t) (hpeak : t ≤ exp (sqrt (a / q))) :
    0 ≤ logDampedPowerSlope a q t := by
  have hlog := (log_le_iff_le_exp (lt_trans zero_lt_one ht)).mpr hpeak
  have hs := pow_le_pow_left₀ (log_pos ht).le hlog 2
  rw [sq_sqrt (div_nonneg ha hq.le)] at hs
  have hmul := mul_le_mul_of_nonneg_left hs hq.le
  have he : q * (a / q) = a := by field_simp
  rw [he] at hmul
  exact div_nonneg (mul_nonneg (logDampedPower_pos _ _ _).le (sub_nonneg.mpr hmul))
    (mul_nonneg (lt_trans zero_lt_one ht).le (sq_nonneg _))

/-- After the turning point the explicit derivative is nonpositive. -/
theorem logDampedPowerSlope_nonpos_after {a q t : ℝ}
    (ha : 0 ≤ a) (hq : 0 < q) (ht : 1 < t) (hpeak : exp (sqrt (a / q)) ≤ t) :
    logDampedPowerSlope a q t ≤ 0 := by
  have hlog := (le_log_iff_exp_le (lt_trans zero_lt_one ht)).mpr hpeak
  have hs := pow_le_pow_left₀ (sqrt_nonneg (a / q)) hlog 2
  rw [sq_sqrt (div_nonneg ha hq.le)] at hs
  have hmul := mul_le_mul_of_nonneg_left hs hq.le
  have he : q * (a / q) = a := by field_simp
  rw [he] at hmul
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (logDampedPower_pos _ _ _).le (sub_nonpos.mpr hmul))
    (mul_nonneg (lt_trans zero_lt_one ht).le (sq_nonneg _))

end

end Real
