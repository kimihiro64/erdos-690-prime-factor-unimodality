import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds

set_option autoImplicit false

/-! # Scalar logarithm bounds for the elementary classification -/

namespace PrimeFactorUnimodality

open Real

theorem log_tangent_upper (x b : Real) (hx : 0 < x) (hb : 0 < b) :
    log x <= log b + x / b - 1 := by
  have h := log_le_sub_one_of_pos (div_pos hx hb)
  rw [log_div hx.ne' hb.ne'] at h
  linarith

theorem log_tangent_lower (x b : Real) (hx : 0 < x) (hb : 0 < b) :
    log b + 1 - b / x <= log x := by
  have h := log_le_sub_one_of_pos (div_pos hb hx)
  rw [log_div hb.ne' hx.ne'] at h
  linarith

theorem log_smooth_ratio (a b c d e f : Nat) :
    log ((2 : Real)^a * 3^b * 5^c / (2^d * 3^e * 5^f)) =
      ((a : Real) - d) * log 2 + ((b : Real) - e) * log 3 +
        ((c : Real) - f) * log 5 := by
  rw [log_div (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  simp only [log_pow]
  ring

theorem log_smooth_tangent_upper (x : Real) (a b c d e f : Nat) (hx : 0 < x) :
    log x <= ((a : Real) - d) * log 2 + ((b : Real) - e) * log 3 +
      ((c : Real) - f) * log 5 +
        x / ((2 : Real)^a * 3^b * 5^c / (2^d * 3^e * 5^f)) - 1 := by
  have h := log_tangent_upper x
    ((2 : Real)^a * 3^b * 5^c / (2^d * 3^e * 5^f)) hx (by positivity)
  rw [log_smooth_ratio] at h
  exact h

theorem log_smooth_tangent_lower (x : Real) (a b c d e f : Nat) (hx : 0 < x) :
    ((a : Real) - d) * log 2 + ((b : Real) - e) * log 3 +
      ((c : Real) - f) * log 5 + 1 -
        ((2 : Real)^a * 3^b * 5^c / (2^d * 3^e * 5^f)) / x <= log x := by
  have h := log_tangent_lower x
    ((2 : Real)^a * 3^b * 5^c / (2^d * 3^e * 5^f)) hx (by positivity)
  rw [log_smooth_ratio] at h
  exact h

theorem log_38000_gt : (10.545 : Real) < log 38000 := by
  have h := log_smooth_tangent_lower 38000 9 1 2 0 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_gt, LogTables.log_3_gt, LogTables.log_5_gt]

theorem log_10545_bounds : And ((2.355 : Real) < log 10.545) (log (10.545 : Real) < 2.356) := by
  have hlo := log_smooth_tangent_lower 10.545 1 3 0 0 0 1 (by norm_num)
  have hup := log_smooth_tangent_upper 10.545 1 3 0 0 0 1 (by norm_num)
  norm_num at hlo hup
  constructor
  next => linarith [LogTables.log_2_gt, LogTables.log_3_gt, LogTables.log_5_lt]
  next => linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_gt]

theorem log_939_lt : log (9.39 : Real) < 2.24 := by
  have h := log_smooth_tangent_upper 9.39 0 1 2 3 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_gt, LogTables.log_3_lt, LogTables.log_5_lt]

theorem log_934_gt : (2.23 : Real) < log 9.34 := by
  have h := log_smooth_tangent_lower 9.34 0 1 2 3 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_3_gt, LogTables.log_5_gt]

theorem log_88_lt : log (8.8 : Real) < 2.175 := by
  have h := log_smooth_tangent_upper 8.8 0 2 3 7 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_gt, LogTables.log_3_lt, LogTables.log_5_lt]

theorem log_18350_lt : log (18350 : Real) < 9.82 := by
  have h := log_smooth_tangent_upper 18350 11 2 0 0 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_3_lt]

theorem log_7340000_lt : log (7340000 : Real) < 15.81 := by
  have h := log_smooth_tangent_upper 7340000 15 2 2 0 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt]

theorem log_6535_gt : (8.78 : Real) < log 6535 := by
  have h := log_smooth_tangent_lower 6535 8 0 2 0 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_gt, LogTables.log_5_gt]

theorem log_11tenth_lt : log (1.1 : Real) < 0.096 := by
  have h := log_smooth_tangent_upper 1.1 0 2 0 3 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_gt, LogTables.log_3_lt]

theorem log_125div77_lt : log ((125 : Real) / 77) < 0.485 := by
  have h := log_smooth_tangent_upper (125/77) 3 0 0 0 0 1 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_5_gt]

theorem log_0979_gt : (-0.022 : Real) < log 0.979 := by
  have h := log_tangent_lower 0.979 1 (by norm_num) (by norm_num)
  norm_num at h
  linarith

theorem log_4752_bounds : And ((8.46 : Real) < log 4752) (log (4752 : Real) < 8.47) := by
  have hlo := log_smooth_tangent_lower 4752 3 0 4 0 0 0 (by norm_num)
  have hup := log_smooth_tangent_upper 4752 3 0 4 0 0 0 (by norm_num)
  norm_num at hlo hup
  constructor
  next => linarith [LogTables.log_2_gt, LogTables.log_5_gt]
  next => linarith [LogTables.log_2_lt, LogTables.log_5_lt]

theorem log_847_lt : log (8.47 : Real) < 2.137 := by
  have h := log_smooth_tangent_upper 8.47 0 0 2 0 1 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_3_gt, LogTables.log_5_lt]

theorem log_38000_lt : log (38000 : Real) < 10.55 := by
  have h := log_smooth_tangent_upper 38000 9 1 2 0 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt]

theorem log_37950_lt : log (37950 : Real) < 10.545 := by
  have h := log_smooth_tangent_upper 37950 9 1 2 0 0 0 (by norm_num)
  norm_num at h
  linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt]

end PrimeFactorUnimodality
