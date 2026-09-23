/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedParameter

/-! # A sharper elementary bound for damped logarithmic tails

An explicit upper primitive retains the sharper coefficient in Dusart's
HDR (2022), Lemma 49. Its derivative is the negative density minus a
nonnegative quadratic correction. The proof uses real calculus directly
and does not require a special-function representation of the integral.
-/

namespace Real

open MeasureTheory Set

/-- An upper primitive for the decreasing logarithmically weighted damped kernel. -/
noncomputable def logDampedTailPrimitive (a m b t : ℝ) : ℝ :=
  logDampedPower a m t * (log t ^ 2 / (m * log t ^ 2 - a)) * (log t + 1 / m - log b)

/-- The upper primitive differentiates to the negative density minus a correction. -/
theorem hasDerivAt_logDampedTailPrimitive {a m b t : ℝ} (hm : 0 < m) (hb : 0 < b)
    (ht : 1 < t) (hD : m * log t ^ 2 - a ≠ 0) :
    HasDerivAt (logDampedTailPrimitive a m b)
      (-log (t / b) * logDampedPower a (m + 1) t -
        (logDampedPower a m t / t) *
          (a * (log t ^ 2 + 2 * (1 / m - log b) * log t + a / m) /
            (m * log t ^ 2 - a) ^ 2)) t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hL := log_pos ht
  have hlog := hasDerivAt_log ht0.ne'
  have hden := ((hlog.pow 2).const_mul m).sub_const a
  have hd := ((hasDerivAt_logDampedPower (a := a) (q := m) ht).mul
    ((hlog.pow 2).div hden hD)).mul ((hlog.add_const (1 / m)).sub_const (log b))
  have hk : logDampedPower a (m + 1) t = logDampedPower a m t / t := by
    rw [logDampedPower_split (p := 1) ht0,
      show m + 1 - 1 = m by ring, rpow_neg_one]
    ring
  convert hd using 1
  · funext t
    rfl
  · dsimp
    rw [hk, log_div ht0.ne' hb.ne']
    have hD' : log t ^ 2 * m - a ≠ 0 := by simpa only [mul_comm] using hD
    field_simp [hm.ne', ht0.ne', hL.ne', hD, hD']
    ring

/-- The parameter condition makes the derivative correction nonnegative. -/
theorem logDampedTail_correction_nonneg {a m b t : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (ht : 1 < t)
    (hparam : log b ≤ 1 / m + sqrt (a / m)) :
    0 ≤ (logDampedPower a m t / t) *
      (a * (log t ^ 2 + 2 * (1 / m - log b) * log t + a / m) /
        (m * log t ^ 2 - a) ^ 2) := by
  have hL : 0 ≤ log t := (log_pos ht).le
  have hs := sq_sqrt (div_nonneg ha hm.le)
  have hP : 0 ≤ log t ^ 2 + 2 * (1 / m - log b) * log t + a / m := by
    have hz : 0 ≤ 1 / m - log b + sqrt (a / m) := by linarith
    nlinarith [mul_nonneg hz hL, sq_nonneg (log t - sqrt (a / m))]
  exact mul_nonneg (div_nonneg (logDampedPower_pos _ _ _).le
    (lt_trans zero_lt_one ht).le) (div_nonneg (mul_nonneg ha hP) (sq_nonneg _))

/-- A strict turning-height margin keeps the denominator positive on the tail. -/
theorem logDampedTail_den_pos {a m u t : ℝ} (hm : 0 < m) (hu : 1 < u)
    (hgap : a < m * log u ^ 2) (hut : u ≤ t) : 0 < m * log t ^ 2 - a := by
  have hs := pow_le_pow_left₀ (log_pos hu).le
    (log_le_log (lt_trans zero_lt_one hu) hut) 2
  exact sub_pos.mpr (hgap.trans_le (mul_le_mul_of_nonneg_left hs hm.le))

/-- The upper primitive is nonnegative beyond the strict turning height. -/
theorem logDampedTailPrimitive_nonneg {a m b u t : ℝ} (hm : 0 < m) (hu : 1 < u)
    (hgap : a < m * log u ^ 2) (hut : u ≤ t)
    (hparam : log b ≤ 1 / m + sqrt (a / m)) : 0 ≤ logDampedTailPrimitive a m b t := by
  have ht : 1 < t := hu.trans_le hut
  have hd := logDampedTail_den_pos hm hu hgap hut
  have hr : sqrt (a / m) ≤ log t := (sqrt_le_left (log_pos ht).le).mpr
    ((div_le_iff₀ hm).mpr (by nlinarith))
  have hl : 0 ≤ log t + 1 / m - log b := by linarith
  unfold logDampedTailPrimitive
  exact mul_nonneg (mul_nonneg (logDampedPower_pos _ _ _).le
    (div_nonneg (sq_nonneg _) hd.le)) hl

/-- The finite density integral is bounded by the drop of the upper primitive. -/
theorem integral_logDampedPower_log_le_sub {a m b u v : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hb : 0 < b) (hu : 1 < u) (huv : u ≤ v)
    (hgap : a < m * log u ^ 2) (hparam : log b ≤ 1 / m + sqrt (a / m)) :
    (∫ t in Icc u v, log (t / b) * logDampedPower a (m + 1) t) ≤
      logDampedTailPrimitive a m b u - logDampedTailPrimitive a m b v := by
  have hpos (t : ℝ) (ht : t ∈ Icc u v) : 1 < t := hu.trans_le ht.1
  have hlog : ContinuousOn (fun t : ℝ => log (t / b)) (Icc u v) :=
    (continuousOn_id.div_const b).log (fun t ht =>
      (div_pos (lt_trans zero_lt_one (hpos t ht)) hb).ne')
  have hd (t : ℝ) (ht : u ≤ t) := hasDerivAt_logDampedTailPrimitive hm hb (hu.trans_le ht)
    (logDampedTail_den_pos hm hu hgap ht).ne'
  have he := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le huv
    (fun t ht => ((hd t ht.1).neg).continuousAt.continuousWithinAt)
    (fun t ht => ((hd t ht.1.le).neg).hasDerivWithinAt)
    (hlog.mul (continuousOn_logDampedPower (a := a) (q := m + 1) hpos)).integrableOn_Icc
    (fun t ht => by
      have hc := logDampedTail_correction_nonneg ha hm (hu.trans ht.1) hparam
      change log (t / b) * logDampedPower a (m + 1) t ≤ _
      linarith only [hc])
  rw [intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc] at he
  simpa only [Pi.mul_apply, Pi.neg_apply, neg_sub_neg] using he

/-- The complete improper density integral satisfies the sharp endpoint bound. -/
theorem integral_logDampedPower_log_tail_le {a m b u : ℝ}
    (ha : 0 ≤ a) (hm : 1 ≤ m) (hb : 0 < b) (hu : 1 < u)
    (hgap : a < m * log u ^ 2) (hparam : log b ≤ 1 / m + sqrt (a / m)) :
    (∫ t in Ioi u, log (t / b) * logDampedPower a (m + 1) t) ≤
      logDampedTailPrimitive a m b u := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hi := integrableOn_log_div_mul_logDampedPower ha (by linarith : 2 ≤ m + 1) hu hb
  have hl := intervalIntegral_tendsto_integral_Ioi u hi Filter.tendsto_id
  apply le_of_tendsto hl
  filter_upwards [Filter.eventually_ge_atTop u] with v huv
  simpa only [id_eq, intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc] using
    (integral_logDampedPower_log_le_sub ha hm0 hb hu huv hgap hparam).trans
      (sub_le_self _ (logDampedTailPrimitive_nonneg hm0 hu hgap huv hparam))

/-- An exponential cutoff gives the sharp elementary tail coefficient. -/
theorem logDampedTailPrimitive_exp {m ν X b : ℝ} (hX : 0 < X) (hν : 0 < ν) :
    logDampedTailPrimitive (X ^ 2) m b (exp (ν * X)) =
      exp (-m * (ν * X) - X / ν) * (ν ^ 2 / (m * ν ^ 2 - 1)) *
        (ν * X + 1 / m - log b) := by
  have he : (ν * X) ^ 2 / (m * (ν * X) ^ 2 - X ^ 2) = ν ^ 2 / (m * ν ^ 2 - 1) := by
    calc
      _ = (ν ^ 2 * X ^ 2) / ((m * ν ^ 2 - 1) * X ^ 2) := by congr 1 <;> ring
      _ = _ := mul_div_mul_right _ _ (pow_ne_zero 2 hX.ne')
  unfold logDampedTailPrimitive
  rw [logDampedPower_nu hX hν, log_exp, he]

end Real
