/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import PrimeFactorUnimodality.Helpers.Analytic.SharpPsiUpper

/-!
# Explicit elementary bounds for Chebyshev's theta function

The sharpened factorial argument and the prime-square subtraction give
uniform rational bounds from 1000, 2000, and the ray beginning at 2^30.
-/

set_option autoImplicit false

namespace Chebyshev

open Real

theorem elementary_log_ray_bounds (B L S x : Real) (hB : 9 <= B) (hx : B <= x)
    (hlog : log B <= L) (hS : 0 < S) (hSq : S ^ 2 <= B) :
    And (log x / sqrt x <= L / S)
      (And (log x <= L / B * x) ((log x) ^ 2 <= (L / S) ^ 2 * x)) := by
  have hBpos : 0 < B := by linarith
  have hxpos : 0 < x := by linarith
  have hexp2 : exp 2 <= B := by
    have he : exp 1 < 3 := exp_one_lt_d9.trans (by norm_num)
    have he2 : exp 2 < 9 := by
      rw [show (2 : Real) = 1 + 1 by norm_num, exp_add]
      nlinarith [exp_pos 1]
    linarith
  have hexp1 : exp 1 <= B := by linarith [exp_one_lt_d9]
  have hL : 0 <= L := (log_nonneg (by linarith)).trans hlog
  have hsB : 0 < sqrt B := sqrt_pos.mpr hBpos
  have hsx : 0 < sqrt x := sqrt_pos.mpr hxpos
  have hSle : S <= sqrt B := by
    nlinarith [sq_sqrt hBpos.le, sqrt_nonneg B]
  have hr := log_div_sqrt_antitoneOn hexp2 (hexp2.trans hx) hx
  change log x / sqrt x <= log B / sqrt B at hr
  have hr' : log x / sqrt x <= L / S := by
    apply hr.trans
    calc
      log B / sqrt B <= L / sqrt B :=
        (div_le_div_iff_of_pos_right hsB).mpr hlog
      _ <= L / S := div_le_div_of_nonneg_left hL hS hSle
  have hself := log_div_self_antitoneOn hexp1 (hexp1.trans hx) hx
  change log x / x <= log B / B at hself
  have hratio : log x / x <= L / B :=
    hself.trans ((div_le_div_iff_of_pos_right hBpos).mpr hlog)
  have hlinear := mul_le_mul_of_nonneg_right hratio hxpos.le
  have hcancel : log x / x * x = log x := by field_simp
  rw [hcancel] at hlinear
  have hratioNonneg : 0 <= log x / sqrt x :=
    div_nonneg (log_nonneg (by linarith)) hsx.le
  have hLS : 0 <= L / S := div_nonneg hL hS.le
  have hquadratic : (log x / sqrt x) ^ 2 <= (L / S) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr') (add_nonneg hratioNonneg hLS)]
  rw [div_pow, sq_sqrt hxpos.le] at hquadratic
  have hscaled := mul_le_mul_of_nonneg_right hquadratic hxpos.le
  have hcancelSq : log x ^ 2 / x * x = log x ^ 2 := by field_simp
  rw [hcancelSq] at hscaled
  exact And.intro hr' (And.intro hlinear hscaled)

private theorem psi_log_sq_coefficient :
    5 / (4 * log (6 : Real)) <= (7 : Real) / 10 := by
  have hl : 0 < log (6 : Real) := log_pos (by norm_num)
  have hlower : (25 : Real) / 14 <= log 6 := by
    rw [show (6 : Real) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith [LogTables.log_2_gt, LogTables.log_3_gt]
  have heq : 5 / (4 * log (6 : Real)) * (4 * log 6) = 5 := by field_simp
  exact le_of_mul_le_mul_right (by rw [heq]; linarith)
    (show 0 < 4 * log (6 : Real) by positivity)

theorem psi_elementary_quadratic_upper (x : Real) (hx : 30 <= x) :
    psi x <= (110556 : Real) / 100000 * x +
      (7 : Real) / 10 * log x ^ 2 + 5 / 4 * log x + 1 := by
  have h := psi_half_upper x hx
  have ha := mul_le_mul_of_nonneg_right a_bound.2 (show 0 <= x by linarith)
  have hq := mul_le_mul_of_nonneg_right psi_log_sq_coefficient (sq_nonneg (log x))
  nlinarith only [h, ha, hq]

theorem theta_half_upper (x : Real) (hx : 900 <= x) :
    theta x <= 6 * a * x / 5 - a * sqrt x +
      5 / (4 * log 6) * log x ^ 2 + 5 / 2 * log x := by
  have hxnonneg : 0 <= x := by linarith
  have hy : 30 <= sqrt x := by nlinarith [sq_sqrt hxnonneg, sqrt_nonneg x]
  have hp := psi_half_upper x (by linarith)
  have hl := psi_half_lower (sqrt x) hy
  have hd := psi_sub_theta_ge_psi_add_psi_add_psi hxnonneg
  have hroot : x ^ (Inv.inv (2 : Real)) = sqrt x := by
    rw [sqrt_eq_rpow, one_div]
  have hd' : psi (sqrt x) <= psi x - theta x := by
    rw [hroot] at hd
    linarith [psi_nonneg (x ^ (Inv.inv (3 : Real))),
      psi_nonneg (x ^ (Inv.inv (7 : Real)))]
  rw [log_sqrt hxnonneg] at hl
  linarith

theorem theta_elementary_quadratic_upper (x : Real) (hx : 900 <= x) :
    theta x <= (110556 : Real) / 100000 * x -
      (92129 : Real) / 100000 * sqrt x +
      (7 : Real) / 10 * log x ^ 2 + 5 / 2 * log x := by
  have h := theta_half_upper x hx
  have ha := mul_le_mul_of_nonneg_right a_bound.2 (show 0 <= x by linarith)
  have hs := mul_le_mul_of_nonneg_right a_bound.1 (sqrt_nonneg x)
  have hq := mul_le_mul_of_nonneg_right psi_log_sq_coefficient (sq_nonneg (log x))
  nlinarith only [h, ha, hs, hq]

private theorem log_1000_lt : log (1000 : Real) < 7 := by
  have h := LogTables.log_le_smooth (x := (1000 : Real)) (a := 3) (b := 0) (c := 3)
    (by norm_num) (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_5_lt]

private theorem log_2000_lt : log (2000 : Real) < 761 / 100 := by
  have h := LogTables.log_le_smooth (x := (2000 : Real)) (a := 4) (b := 0) (c := 3)
    (by norm_num) (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_5_lt]

private theorem log_3000_lt : log (3000 : Real) < 81 / 10 := by
  have h := LogTables.log_le_smooth (x := (3000 : Real)) (a := 3) (b := 1) (c := 3)
    (by norm_num) (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt]

private theorem log_6000_lt : log (6000 : Real) < 87 / 10 := by
  have h := LogTables.log_le_smooth (x := (6000 : Real)) (a := 4) (b := 1) (c := 3)
    (by norm_num) (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt]

theorem log_le_seven_thousandths_mul (x : Real) (hx : 1000 <= x) :
    log x <= (7 : Real) / 1000 * x :=
  (elementary_log_ray_bounds 1000 7 31 x (by norm_num) hx log_1000_lt.le
    (by norm_num) (by norm_num)).2.1

theorem psi_upper_116_from_1000 (x : Real) (hx : 1000 <= x) :
    psi x <= (116 : Real) / 100 * x := by
  have hr := elementary_log_ray_bounds 1000 7 31 x (by norm_num) hx log_1000_lt.le
    (by norm_num) (by norm_num)
  have hp := psi_elementary_quadratic_upper x (by linarith)
  nlinarith [hr.2.1, hr.2.2]

theorem theta_upper_116_from_1000 (x : Real) (hx : 1000 <= x) :
    theta x <= (116 : Real) / 100 * x :=
  (theta_le_psi x).trans (psi_upper_116_from_1000 x hx)

theorem theta_upper_112_from_2000 (x : Real) (hx : 2000 <= x) :
    theta x <= (112 : Real) / 100 * x := by
  by_cases h3000 : x <= 3000
  case pos =>
    have hr := elementary_log_ray_bounds 2000 (761 / 100) 44 x (by norm_num) hx log_2000_lt.le
      (by norm_num) (by norm_num)
    have ht := theta_elementary_quadratic_upper x (by linarith)
    have hs : sqrt x <= 55 := by nlinarith [sq_sqrt (show 0 <= x by linarith), sqrt_nonneg x]
    have hsx : x <= 55 * sqrt x := by
      nlinarith [mul_nonneg (sqrt_nonneg x) (sub_nonneg.mpr hs),
        sq_sqrt (show 0 <= x by linarith)]
    nlinarith [hr.2.1, hr.2.2]
  case neg =>
    by_cases h6000 : x <= 6000
    case pos =>
      have hr := elementary_log_ray_bounds 3000 (81 / 10) 54 x (by norm_num) (by linarith)
        log_3000_lt.le (by norm_num) (by norm_num)
      have ht := theta_elementary_quadratic_upper x (by linarith)
      have hs : sqrt x <= 78 := by nlinarith [sq_sqrt (show 0 <= x by linarith), sqrt_nonneg x]
      have hsx : x <= 78 * sqrt x := by
        nlinarith [mul_nonneg (sqrt_nonneg x) (sub_nonneg.mpr hs),
          sq_sqrt (show 0 <= x by linarith)]
      nlinarith [hr.2.1, hr.2.2]
    case neg =>
      have hr := elementary_log_ray_bounds 6000 (87 / 10) 77 x (by norm_num) (by linarith)
        log_6000_lt.le (by norm_num) (by norm_num)
      have hp := psi_elementary_quadratic_upper x (by linarith)
      have ht := theta_le_psi x
      nlinarith [hr.2.1, hr.2.2]

private theorem theta_lower_of_log_bounds (x L R : Real) (hx : 30 <= x)
    (hlog : log x <= L * x) (hratio : log x / sqrt x <= R) :
    ((92129 : Real) / 100000 - 5 / 2 * L - 2 * R) * x + 1 <= theta x := by
  have hp := psi_half_lower x hx
  have hd := psi_sub_theta_le (x := x) (by linarith)
  have ha := mul_le_mul_of_nonneg_right a_bound.1 (show 0 <= x by linarith)
  have hs : 0 < sqrt x := sqrt_pos.mpr (by linarith)
  have scaled := mul_le_mul_of_nonneg_left hratio (show 0 <= 2 * x by positivity)
  have hid : 2 * x * (log x / sqrt x) = 2 * sqrt x * log x := by
    field_simp [hs.ne']
    rw [sq_sqrt (show 0 <= x by linarith)]
    ring
  rw [hid] at scaled
  nlinarith only [hp, hd, ha, hlog, scaled]

theorem theta_lower_040_from_1000 (x : Real) (hx : 1000 <= x) :
    (4 : Real) / 10 * x <= theta x := by
  have hr := elementary_log_ray_bounds 1000 7 31 x (by norm_num) hx log_1000_lt.le
    (by norm_num) (by norm_num)
  have ht := theta_lower_of_log_bounds x (7 / 1000) (7 / 31) (by linarith)
    hr.2.1 hr.1
  nlinarith

theorem theta_lower_092_from_pow30 (x : Real) (hx : (2 : Real) ^ (30 : Nat) <= x) :
    (92 : Real) / 100 * x <= theta x := by
  have hlog : log ((2 : Real) ^ (30 : Nat)) <= 21 := by
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [LogTables.log_2_lt]
  have hr := elementary_log_ray_bounds ((2 : Real) ^ (30 : Nat)) 21 32768 x (by norm_num) hx
    hlog (by norm_num) (by norm_num)
  have ht := theta_lower_of_log_bounds x (21 / ((2 : Real) ^ (30 : Nat))) (21 / 32768)
    (by norm_num at hx; linarith) hr.2.1 hr.1
  norm_num at hx ht
  nlinarith

end Chebyshev
