/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPrimeKernel

/-!
# The retained main integral in the smoothed prime bound

The comparison keeps both intervals [1000,t] and [t,X]. Their log(2)
terms cancel exactly, leaving the stated logarithmic endpoint loss.
-/

set_option autoImplicit false

namespace Mertens

open Real MeasureTheory

noncomputable def smoothedMainIntegrand (t u : Real) : Real := 1 / ((u + t) * log u)

theorem smoothedMainIntegrand_continuousOn (t a b : Real) (ht : 0 < t)
    (ha : 1000 <= a) :
    ContinuousOn (smoothedMainIntegrand t) (Set.Icc a b) := by
  intro u hu
  have hup : 0 < u := by have h := hu.1; linarith
  have hlog : Not (log u = 0) := ne_of_gt (log_pos (by have h := hu.1; linarith))
  have hplus : Not (u + t = 0) := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold smoothedMainIntegrand
  fun_prop (disch := grind)

theorem smoothedMainIntegral_lower (t X : Real) (ht : 4752 <= t) (htX : t <= X) :
    log (log X) - log (log t) - log (1 + 1000 / t) / log t <=
      intervalIntegral (smoothedMainIntegrand t) 1000 X volume := by
  have htpos : 0 < t := by linarith
  have hYt : (1000 : Real) <= t := by linarith
  have hX : 1000 <= X := hYt.trans htX
  have hXpos : 0 < X := by linarith
  have htlog := log_gt_three_from_1000 t hYt
  have htlogpos : 0 < log t := by linarith
  have htlog0 : Not (log t = 0) := htlogpos.ne'
  have hiLow : IntervalIntegrable (smoothedMainIntegrand t) volume 1000 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYt).mpr
      (smoothedMainIntegrand_continuousOn t 1000 t htpos (by norm_num)).integrableOn_Icc
  have hiHigh : IntervalIntegrable (smoothedMainIntegrand t) volume t X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le htX).mpr
      (smoothedMainIntegrand_continuousOn t t X htpos hYt).integrableOn_Icc
  have hiH : IntervalIntegrable (fun u => 1 / ((u + t) * log t)) volume 1000 t := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hYt).mpr
    apply ContinuousOn.integrableOn_Icc
    intro u hu
    have hplus : Not (u + t = 0) := by have hh := hu.1; linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := grind)
  have hH : intervalIntegral (fun u => 1 / ((u + t) * log t)) 1000 t volume =
      log (t + t) / log t - log (1000 + t) / log t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => log (u + t) / log t)
    next =>
      intro u hu
      rw [Set.uIcc_of_le hYt] at hu
      have hplus : Not (u + t = 0) := by have hh := hu.1; linarith
      convert! (((hasDerivAt_id' u).add_const t).log hplus).div_const (log t) using 1
      field_simp
    next => exact hiH
  have hLow := intervalIntegral.integral_mono_on hYt hiH hiLow (fun u hu => by
    have hup : 0 < u := by have hh := hu.1; linarith
    have hlogpos : 0 < log u := log_pos (by have hh := hu.1; linarith)
    have hlogle : log u <= log t := log_le_log hup hu.2
    unfold smoothedMainIntegrand
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos (by linarith) hlogpos)
      (mul_le_mul_of_nonneg_left hlogle (by linarith)))
  rw [hH] at hLow
  have hLogTwice : log (t + t) = log 2 + log t := by
    rw [show t + t = 2 * t by ring, log_mul (by norm_num) htpos.ne']
  have hLogStart : log (1000 + t) = log t + log (1 + 1000 / t) := by
    have heq : (1000 : Real) + t = t * (1 + 1000 / t) := by field_simp; ring
    rw [heq, log_mul htpos.ne' (by positivity)]
  have hLowDiff : log (t + t) / log t - log (1000 + t) / log t =
      log 2 / log t - log (1 + 1000 / t) / log t := by
    rw [hLogTwice, hLogStart]
    ring
  rw [hLowDiff] at hLow
  let F : Real -> Real := fun u => log (log u) + (log (u + t) - log u) / log t
  let FP : Real -> Real := fun u => 1 / (u * log u) + (1 / (u + t) - 1 / u) / log t
  have hiFP : IntervalIntegrable FP volume t X := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le htX).mpr
    apply ContinuousOn.integrableOn_Icc
    intro u hu
    have hup : 0 < u := htpos.trans_le hu.1
    have hu0 : Not (u = 0) := hup.ne'
    have hlog0 : Not (log u = 0) := ne_of_gt (log_pos (by have hh := hu.1; linarith))
    have hplus0 : Not (u + t = 0) := by linarith
    apply ContinuousAt.continuousWithinAt
    dsimp only [FP]
    fun_prop (disch := grind)
  have hF : intervalIntegral FP t X volume = F X - F t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
    next =>
      intro u hu
      rw [Set.uIcc_of_le htX] at hu
      have hup : 0 < u := htpos.trans_le hu.1
      have hu0 : Not (u = 0) := hup.ne'
      have hlog0 : Not (log u = 0) := ne_of_gt (log_pos (by have hh := hu.1; linarith))
      have hplus0 : Not (u + t = 0) := by linarith
      dsimp only [F, FP]
      convert! ((hasDerivAt_log hu0).log hlog0).add
        ((((hasDerivAt_id' u).add_const t).log hplus0).sub (hasDerivAt_log hu0) |>.div_const (log t))
        using 1 <;> field_simp <;> ring
    next => exact hiFP
  have hHigh := intervalIntegral.integral_mono_on htX hiFP hiHigh (fun u hu => by
    have hup : 0 < u := htpos.trans_le hu.1
    have hu0 : Not (u = 0) := hup.ne'
    have hlogpos : 0 < log u := log_pos (by have hh := hu.1; linarith)
    have hlog0 : Not (log u = 0) := hlogpos.ne'
    have hplus0 : Not (u + t = 0) := by linarith
    have hlogle : log t <= log u := log_le_log htpos hu.1
    have hinv : 1 / log u <= 1 / log t :=
      div_le_div_of_nonneg_left (by norm_num) htlogpos hlogle
    have hcoef : 0 <= t / (u * (u + t)) := by positivity
    have heq : FP u = smoothedMainIntegrand t u -
        (t / (u * (u + t))) * (1 / log t - 1 / log u) := by
      dsimp only [FP, smoothedMainIntegrand]
      field_simp
      ring
    rw [heq]
    exact sub_le_self _ (mul_nonneg hcoef (sub_nonneg.mpr hinv)))
  rw [hF] at hHigh
  have hFX : log (log X) <= F X := by
    have hdiff : 0 <= log (X + t) - log X :=
      sub_nonneg.mpr (log_le_log hXpos (by linarith))
    dsimp only [F]
    exact le_add_of_nonneg_right (div_nonneg hdiff htlogpos.le)
  have hFt : F t = log (log t) + log 2 / log t := by
    dsimp only [F]
    rw [hLogTwice]
    ring
  rw [hFt] at hHigh
  have hsum := intervalIntegral.integral_add_adjacent_intervals hiLow hiHigh
  linarith only [hLow, hHigh, hFX, hsum]

end Mertens
