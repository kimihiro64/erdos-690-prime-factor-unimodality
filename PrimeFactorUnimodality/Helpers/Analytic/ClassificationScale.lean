import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PrimeFactorUnimodality.Helpers.Analytic.ClassificationScalarLogs

set_option autoImplicit false

/-! # The elementary scale on the infinite classification range -/

namespace PrimeFactorUnimodality

open Real

noncomputable def classificationH (v : Real) : Real := v - log v + 1.2
noncomputable def classificationLogEll (v : Real) : Real := v - log (1.1 * classificationH v)
noncomputable def classificationEll (r : Real) : Real := r / (1.1 * classificationH (log r))

theorem classificationH_bounds (v : Real) (hv : 10.545 <= v) :
    And (9.34 < classificationH v)
      (And (classificationH v < v) (0.89 * v <= classificationH v)) := by
  have hvpos : 0 < v := by linarith
  have hlower : (2.355 : Real) < log v :=
    log_10545_bounds.1.trans_le (log_le_log (by norm_num) hv)
  have hupper := log_tangent_upper v 10.545 hvpos (by norm_num)
  have hbase := log_10545_bounds.2
  unfold classificationH
  norm_num at hupper
  constructor
  next => nlinarith
  next =>
    constructor
    next => linarith
    next => nlinarith

theorem classificationH_hasDerivAt (v : Real) (hv : 0 < v) :
    HasDerivAt classificationH (1 - 1 / v) v := by
  unfold classificationH
  convert! ((hasDerivAt_id' v).sub (hasDerivAt_log hv.ne')).add_const 1.2 using 1 <;> ring

theorem classificationLogEll_hasDerivAt (v : Real) (hv : 10.545 <= v) :
    HasDerivAt classificationLogEll (1 - (1 - 1 / v) / classificationH v) v := by
  have hH := (classificationH_bounds v hv).1
  have hvpos : 0 < v := by linarith
  have hH0 : Not (classificationH v = 0) := by linarith
  unfold classificationLogEll
  convert! (hasDerivAt_id' v).sub
    (((classificationH_hasDerivAt v hvpos).const_mul 1.1).log (by positivity)) using 1
  field_simp
  <;> ring

theorem classificationLogEll_monotone :
    MonotoneOn classificationLogEll (Set.Ici 10.545) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 10.545)
  next =>
    intro v hv
    exact (classificationLogEll_hasDerivAt v hv).continuousAt.continuousWithinAt
  next =>
    intro v hv
    simp only [interior_Ici, Set.mem_Ioi] at hv
    exact (classificationLogEll_hasDerivAt v hv.le).differentiableAt.differentiableWithinAt
  next =>
    intro v hv
    simp only [interior_Ici, Set.mem_Ioi] at hv
    rw [(classificationLogEll_hasDerivAt v hv.le).deriv]
    have hH := (classificationH_bounds v hv.le).1
    have hvpos : 0 < v := by linarith
    have hnum : 1 - 1 / v <= 1 := by linarith [one_div_pos.mpr hvpos]
    have hfrac := (div_le_div_of_nonneg_right hnum (by linarith : 0 <= classificationH v)).trans
      (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 9) (by linarith))
    linarith

theorem exp_classificationLogEll (v : Real) (hv : 10.545 <= v) :
    exp (classificationLogEll v) = exp v / (1.1 * classificationH v) := by
  have hH := (classificationH_bounds v hv).1
  unfold classificationLogEll
  rw [exp_sub, exp_log (by positivity)]

theorem classificationEll_lower (r : Real) (hr : 38000 <= r) :
    (3670 : Real) < classificationEll r := by
  have hrpos : 0 < r := by linarith
  have hv : 10.545 <= log r := log_38000_gt.le.trans (log_le_log (by norm_num) hr)
  have hmon := classificationLogEll_monotone
    (by change (10.545 : Real) <= 10.545; exact le_rfl) hv hv
  have hExp := exp_le_exp.mpr hmon
  rw [exp_classificationLogEll _ (by rfl), exp_classificationLogEll _ hv,
    exp_log hrpos] at hExp
  have hexp : (37950 : Real) < exp 10.545 := by
    calc
      37950 = exp (log (37950 : Real)) := (exp_log (by norm_num)).symm
      _ < exp 10.545 := exp_lt_exp.mpr log_37950_lt
  have hH0 : classificationH 10.545 < 9.39 := by
    unfold classificationH
    linarith [log_10545_bounds.1]
  have hHpos : 0 < classificationH 10.545 := by
    linarith [(classificationH_bounds 10.545 (by rfl)).1]
  have hbase : (3670 : Real) < exp 10.545 / (1.1 * classificationH 10.545) := by
    have hden0 : Not (1.1 * classificationH 10.545 = 0) := by positivity
    have heq : exp 10.545 / (1.1 * classificationH 10.545) *
        (1.1 * classificationH 10.545) = exp 10.545 := by field_simp
    apply lt_of_mul_lt_mul_right (a := 1.1 * classificationH 10.545) _ (by positivity)
    rw [heq]
    nlinarith
  exact hbase.trans_le hExp

end PrimeFactorUnimodality
