import PrimeFactorUnimodality.Helpers.Analytic.ClassificationDescentReserve
import PrimeFactorUnimodality.Helpers.Analytic.ClassificationWindowScalars

set_option autoImplicit false

/-! # The uniform strict descent margin -/

namespace PrimeFactorUnimodality

open Real

private theorem quotient_lt (a b c : Real) (hb : 0 < b) (h : a < c * b) :
    a / b < c := by
  have hb0 : Not (b = 0) := hb.ne'
  have heq : a / b * b = a := by field_simp
  exact lt_of_mul_lt_mul_right (by rw [heq]; exact h) hb.le

theorem classification_logEll (r : Real) (hr : 38000 <= r) :
    log (classificationEll r) =
      log r - log (1.1 : Real) - log (classificationH (log r)) := by
  have hv : 10.545 <= log r := log_38000_gt.le.trans (log_le_log (by norm_num) hr)
  have hH := (classificationH_bounds (log r) hv).1
  have hrpos : 0 < r := by linarith
  unfold classificationEll
  rw [log_div hrpos.ne' (by positivity), log_mul (by norm_num) (by linarith)]
  ring

theorem classification_logT_bounds (r : Real) (hr : 38000 <= r) :
    And (8.78 < log (classificationT r))
      (log (classificationT r) < classificationJ (log r)) := by
  have he := classificationEll_lower r hr
  have ht := classificationT_lower r hr
  have htpos : 0 < classificationT r := by linarith
  have hU : 0 < log (5 * classificationEll r) := log_pos (by linarith)
  have htupper : classificationT r < (25 / 14 : Real) * classificationEll r := by
    unfold classificationT
    linarith
  have hlogupper := log_lt_log htpos htupper
  rw [log_mul (by norm_num) (by linarith), classification_logEll r hr] at hlogupper
  have hcoeff : log ((25 : Real) / 14) - log (1.1 : Real) < 0.485 := by
    rw [<- log_div (by norm_num) (by norm_num)]
    convert log_125div77_lt using 1 <;> norm_num
  constructor
  next => exact log_6535_gt.trans (log_lt_log (by norm_num) ht)
  next =>
    unfold classificationJ
    linarith

noncomputable def classificationDescentBracket (r : Real) : Real :=
  log (classificationEll r) - log (log (classificationT r)) -
    log (1 + 1000 / classificationT r) / log (classificationT r) -
      (11 / 5 : Real) / (log (classificationT r) + 2)

theorem classificationDescentBracket_lower (r : Real) (hr : 38000 <= r) :
    0.618 * classificationH (log r) < classificationDescentBracket r := by
  have hv : 10.545 <= log r := log_38000_gt.le.trans (log_le_log (by norm_num) hr)
  have ht := classificationT_lower r hr
  have htpos : 0 < classificationT r := by linarith
  have hlogs := classification_logT_bounds r hr
  have hlogpos : 0 < log (classificationT r) := by linarith [hlogs.1]
  have hloglog := log_lt_log hlogpos hlogs.2
  have hfrac : (1000 : Real) / classificationT r < 0.154 := by
    apply quotient_lt _ _ _ htpos
    nlinarith
  have hnum : log (1 + 1000 / classificationT r) < 0.154 := by
    have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + 1000 / classificationT r)
    linarith
  have hpen : log (1 + 1000 / classificationT r) / log (classificationT r) <
      0.154 / 8.78 := by
    apply quotient_lt _ _ _ hlogpos
    nlinarith [hlogs.1]
  have herr : (11 / 5 : Real) / (log (classificationT r) + 2) < 2.2 / 10.78 := by
    apply quotient_lt _ _ _ (by linarith : 0 < log (classificationT r) + 2)
    nlinarith [hlogs.1]
  have hreserve := classificationDescentReserve_pos (log r) hv
  unfold classificationDescentReserve at hreserve
  unfold classificationDescentBracket
  rw [classification_logEll r hr]
  linarith [log_11tenth_lt]

theorem classification_descent_scalar (r : Real) (hr : 38000 <= r) :
    (2001 / 2000 : Real) * r <
      classificationT r * classificationDescentBracket r := by
  have hv : 10.545 <= log r := log_38000_gt.le.trans (log_le_log (by norm_num) hr)
  have hH := (classificationH_bounds (log r) hv).1
  have he := classificationEll_lower r hr
  have hU := (classification_window_allowances (classificationEll r) he.le).1
  have ht : (25 / 14 : Real) * 0.9973 * classificationEll r < classificationT r := by
    unfold classificationT
    linarith
  have hB := classificationDescentBracket_lower r hr
  have hprod := mul_lt_mul ht hB.le (by positivity : (0 : Real) < 0.618 * classificationH (log r))
    (by linarith [classificationT_lower r hr] : 0 <= classificationT r)
  have hH0 : Not (1.1 * classificationH (log r) = 0) := by positivity
  have heq : classificationEll r * (1.1 * classificationH (log r)) = r := by
    unfold classificationEll
    field_simp
  nlinarith only [hprod, heq, hr]

end PrimeFactorUnimodality
