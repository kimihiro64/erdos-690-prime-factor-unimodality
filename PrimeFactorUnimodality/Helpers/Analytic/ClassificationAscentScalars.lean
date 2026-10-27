import PrimeFactorUnimodality.Helpers.Analytic.ClassificationDescentScalars

set_option autoImplicit false

/-! # The uniform strict ascent margin -/

namespace PrimeFactorUnimodality

open Real

theorem classification_logEll_upper (r : Real) (hr : 38000 <= r) :
    log (classificationEll r) + 1.1 < classificationH (log r) - 0.078 := by
  have hrpos : 0 < r := by linarith
  have hv : 10.545 <= log r := log_38000_gt.le.trans (log_le_log (by norm_num) hr)
  have hvpos : 0 < log r := by linarith
  have hH := classificationH_bounds (log r) hv
  have hHpos : 0 < classificationH (log r) := by linarith [hH.1]
  have hq : (0.979 : Real) <= 1.1 * classificationH (log r) / log r := by
    have hv0 : Not (log r = 0) := hvpos.ne'
    have heq : 1.1 * classificationH (log r) / log r * log r =
        1.1 * classificationH (log r) := by field_simp
    have hprod : 0.979 * log r <=
        (1.1 * classificationH (log r) / log r) * log r := by
      rw [heq]
      nlinarith [hH.2.2]
    exact le_of_mul_le_mul_right hprod hvpos
  have hlogq : (-0.022 : Real) < log (1.1 * classificationH (log r) / log r) :=
    log_0979_gt.trans_le (log_le_log (by norm_num) hq)
  rw [log_div (by positivity) hvpos.ne', log_mul (by norm_num) hHpos.ne'] at hlogq
  rw [classification_logEll r hr]
  unfold classificationH at hlogq
  unfold classificationH
  linarith

theorem classificationMStar_lower (r : Real) (hr : 38000 <= r) :
    classificationEll r < classificationMStar r := by
  have he := classificationEll_lower r hr
  have hlog : 0 < log (2000 * classificationEll r) := log_pos (by linarith)
  unfold classificationMStar
  linarith

theorem classification_ascent_scalar (r : Real) (hr : 38000 <= r) :
    (1.09 * classificationMStar r + 2) *
      (log (classificationMStar r) + 1.1 + 4 / classificationMStar r) < r := by
  have he := classificationEll_lower r hr
  have hMlo := classificationMStar_lower r hr
  have hMhi := classificationMStar_upper r hr
  have hMpos : 0 < classificationMStar r := by linarith
  have hepos : 0 < classificationEll r := by linarith
  have hlogM : log (classificationMStar r) < log (classificationEll r) + 0.005 := by
    have h := log_lt_log hMpos hMhi
    rw [log_mul (by norm_num) hepos.ne'] at h
    have hc := log_le_sub_one_of_pos (by norm_num : (0 : Real) < 1.005)
    linarith
  have herr : (4 : Real) / classificationMStar r < 4 / 3670 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
  have hbracket : log (classificationMStar r) + 1.1 + 4 / classificationMStar r <
      classificationH (log r) := by
    linarith [classification_logEll_upper r hr]
  have hcoef : 1.09 * classificationMStar r + 2 < 1.1 * classificationEll r := by
    nlinarith
  have hbracketpos : 0 < log (classificationMStar r) + 1.1 + 4 / classificationMStar r := by
    have hl : 0 <= log (classificationMStar r) := log_nonneg (by linarith)
    have hd : 0 <= (4 : Real) / classificationMStar r := by positivity
    linarith
  have hHpos : 0 < classificationH (log r) := by
    have hv : 10.545 <= log r := log_38000_gt.le.trans (log_le_log (by norm_num) hr)
    linarith [(classificationH_bounds (log r) hv).1]
  have hprod := mul_lt_mul hcoef hbracket.le hbracketpos (by positivity : 0 <= 1.1 * classificationEll r)
  have hH0 : Not (1.1 * classificationH (log r) = 0) := by positivity
  have heq : classificationEll r * (1.1 * classificationH (log r)) = r := by
    unfold classificationEll
    field_simp
  nlinarith only [hprod, heq]

end PrimeFactorUnimodality
