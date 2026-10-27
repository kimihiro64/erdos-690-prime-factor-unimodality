/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SharpMertensWeighted

/-!
# A rational upper bound for the Meissel--Mertens constant

The fiftieth harmonic approximation bounds Euler's constant by 59/100.
Five negative prime summands then give M < 29/100.
-/

set_option autoImplicit false

namespace Mertens

open Real Finset

theorem M_eq_eulerMascheroni_add_sum :
    M = eulerMascheroniConstant + tsum M_eq_summand := by
  have h := M.eq
  convert h using 1
  congr 1
  symm
  have hzero := sum_mangoldt_div_log_eq (2 : Real)
  change _ = log (log (2 : Real)) + eulerMascheroniConstant +
    (_ - log (log (2 : Real)) - _) at hzero
  linarith

theorem eulerMascheroniConstant_lt_059 :
    eulerMascheroniConstant < (59 : Real) / 100 := by
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 50
  norm_num [eulerMascheroniSeq'] at h
  have hH : (harmonic 50 : Real) < (9 : Real) / 2 := by norm_num [harmonic]
  have hlog := LogTables.smooth_log_le (x := (50 : Real)) (a := 1) (b := 0) (c := 2)
    (by norm_num) (by norm_num)
  norm_num at hlog
  linarith [LogTables.log_2_gt, LogTables.log_5_gt]

private theorem log_7_gt_19458 : (19458 : Real) / 10000 < log 7 := by
  have h := LogTables.smooth_log_le (x := (7 : Real) ^ (4 : Nat))
    (a := 5) (b := 1) (c := 2) (by positivity) (by norm_num)
  rw [log_pow] at h
  norm_num at h
  linarith [LogTables.log_2_gt, LogTables.log_3_gt, LogTables.log_5_gt]

private theorem log_11_gt_23965 : (23965 : Real) / 10000 < log 11 := by
  have h := LogTables.smooth_log_le (x := (11 : Real) ^ (5 : Nat))
    (a := 8) (b := 0) (c := 4) (by positivity) (by norm_num)
  rw [log_pow] at h
  norm_num at h
  linarith [LogTables.log_2_gt, LogTables.log_5_gt]

theorem M_eq_summand_nonpos (n : Nat) : M_eq_summand n <= 0 := by
  unfold M_eq_summand
  split_ifs with hp
  case pos =>
    have hp2 : (2 : Real) <= n := by exact_mod_cast hp.two_le
    have hf : (1 : Real) / n <= 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    have hlog := log_le_sub_one_of_pos (show (0 : Real) < 1 - 1 / n by linarith)
    linarith
  case neg => rfl

theorem M_lt_029 : M < (29 : Real) / 100 := by
  have hfinite := M_eq_summable.neg.sum_le_tsum (Finset.range 12)
    (fun n _ => neg_nonneg.mpr (M_eq_summand_nonpos n))
  rw [tsum_neg, Finset.sum_neg_distrib] at hfinite
  have hsum : tsum M_eq_summand <= (Finset.range 12).sum M_eq_summand := by linarith
  norm_num [Finset.sum_range_succ, M_eq_summand] at hsum
  have hM := M_eq_eulerMascheroni_add_sum
  rw [hM]
  have hgamma := eulerMascheroniConstant_lt_059
  rw [log_div (by norm_num) (by norm_num),
    log_div (by norm_num) (by norm_num),
    log_div (by norm_num) (by norm_num),
    log_div (by norm_num) (by norm_num),
    log_div (by norm_num) (by norm_num)] at hsum
  rw [show (4 : Real) = 2 * 2 by norm_num, log_mul (by norm_num) (by norm_num),
    show (6 : Real) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num),
    show (10 : Real) = 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num)] at hsum
  rw [log_one] at hsum
  linarith [log_7_gt_19458, log_11_gt_23965, LogTables.log_2_lt]

end Mertens
