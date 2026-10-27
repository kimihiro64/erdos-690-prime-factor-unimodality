import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import PrimeFactorUnimodality.Helpers.Analytic.ClassificationScale

set_option autoImplicit false

/-! # Uniform logarithmic allowances for the primorial window -/

namespace PrimeFactorUnimodality

open Real

theorem log_mul_linear_bound (c B L x : Real)
    (hc : 0 < c) (hB : 0 < B) (hbase : 3 <= c * B)
    (hlog : log (c * B) <= L) (hx : B <= x) :
    log (c * x) <= L / B * x := by
  have hxpos : 0 < x := hB.trans_le hx
  have hexp : exp 1 <= c * B := (exp_one_lt_d9.trans (by norm_num)).le.trans hbase
  have hcx : c * B <= c * x := mul_le_mul_of_nonneg_left hx hc.le
  have h := log_div_self_antitoneOn hexp (hexp.trans hcx) hcx
  change log (c * x) / (c * x) <= log (c * B) / (c * B) at h
  have hscale := mul_le_mul_of_nonneg_right h (mul_pos hc hxpos).le
  have hcancel : log (c * x) / (c * x) * (c * x) = log (c * x) := by field_simp
  have hfactor : log (c * B) / (c * B) * (c * x) = log (c * B) / B * x := by
    field_simp
    <;> ring
  rw [hcancel, hfactor] at hscale
  apply hscale.trans
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlog hB.le) hxpos.le

theorem classification_window_allowances (ell : Real) (hell : 3670 <= ell) :
    And (log (5 * ell) < 0.0027 * ell) (log (2000 * ell) < 0.005 * ell) := by
  have hellpos : 0 < ell := by linarith
  constructor
  next =>
    have h := log_mul_linear_bound 5 3670 9.82 ell (by norm_num) (by norm_num)
      (by norm_num) (by convert log_18350_lt.le using 1 <;> norm_num) hell
    have hs : (9.82 / 3670 : Real) < 0.0027 := by norm_num
    exact h.trans_lt (mul_lt_mul_of_pos_right hs hellpos)
  next =>
    have h := log_mul_linear_bound 2000 3670 15.81 ell (by norm_num) (by norm_num)
      (by norm_num) (by convert log_7340000_lt.le using 1 <;> norm_num) hell
    have hs : (15.81 / 3670 : Real) < 0.005 := by norm_num
    exact h.trans_lt (mul_lt_mul_of_pos_right hs hellpos)

noncomputable def classificationT (r : Real) : Real :=
  (25 / 14 : Real) * (classificationEll r - log (5 * classificationEll r))

noncomputable def classificationMStar (r : Real) : Real :=
  classificationEll r + log (2000 * classificationEll r)

theorem classificationT_lower (r : Real) (hr : 38000 <= r) :
    (6535 : Real) < classificationT r := by
  have he := classificationEll_lower r hr
  have hU := (classification_window_allowances (classificationEll r) he.le).1
  unfold classificationT
  nlinarith

theorem classificationMStar_upper (r : Real) (hr : 38000 <= r) :
    classificationMStar r < 1.005 * classificationEll r := by
  have he := classificationEll_lower r hr
  have hU := (classification_window_allowances (classificationEll r) he.le).2
  unfold classificationMStar
  linarith

end PrimeFactorUnimodality
