import PrimeFactorUnimodality.Helpers.Analytic.ClassificationScalarLogs
import PrimeFactorUnimodality.Helpers.Analytic.ShiftedReciprocalUpper
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPrimeAbel

set_option autoImplicit false

/-! # Elementary scalar bounds for the existing record witnesses -/

namespace PrimeFactorUnimodality

open Real

private theorem quotient_lt (a b c : Real) (hb : 0 < b) (h : a < c * b) :
    a / b < c := by
  have hb0 : Not (b = 0) := hb.ne'
  have heq : a / b * b = a := by field_simp
  exact lt_of_mul_lt_mul_right (by rw [heq]; exact h) hb.le

theorem record_smoothed_sum_lower (X : Real) (hX : 4752 <= X)
    (hlog : 10.6 < log (log X)) :
    (38776 : Real) < 4752 * Mertens.smoothedPrimeSum 4752 X := by
  have htlog := log_4752_bounds
  have hpos : 0 < log (4752 : Real) := by linarith [htlog.1]
  have hloglog : log (log (4752 : Real)) < 2.137 :=
    (log_lt_log hpos htlog.2).trans log_847_lt
  have hpen : log (1 + 1000 / (4752 : Real)) / log 4752 < 0.7 / 8.46 := by
    have hnum : log (1 + 1000 / (4752 : Real)) < 0.7 :=
      (log_lt_log (by norm_num) (by norm_num : 1 + 1000 / (4752 : Real) < 2)).trans
        (LogTables.log_2_lt.trans (by norm_num))
    apply quotient_lt _ _ _ hpos
    nlinarith [htlog.1]
  have herr : (11 / 5 : Real) / (log 4752 + 2) < 2.2 / 10.46 := by
    apply quotient_lt _ _ _ (by linarith : 0 < log (4752 : Real) + 2)
    nlinarith [htlog.1]
  have hmain := Mertens.smoothedPrimeSum_lower 4752 X (by norm_num) hX
  have hbracket : (8.16 : Real) <
      log (log X) - log (log 4752) - log (1 + 1000 / (4752 : Real)) / log 4752 -
        (11 / 5 : Real) / (log 4752 + 2) := by
    linarith only [hlog, hloglog, hpen, herr]
  nlinarith only [hmain, hbracket]

theorem record_shifted_sum_upper (X : Real) (hX : 1000 <= X)
    (hlo : 9 < log X) (hhi : log (log X) < 12.1) :
    3 * Mertens.primeShiftedReciprocalSum X < 48 := by
  have hupper := Mertens.primeShiftedReciprocalSum_upper_four X hX
  have herror : (4 : Real) / log X < 4 / 9 := by
    apply quotient_lt _ _ _ (by linarith : 0 < log X)
    nlinarith
  linarith

end PrimeFactorUnimodality
