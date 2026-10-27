import PrimeFactorUnimodality.Helpers.Analytic.ClassificationScale

set_option autoImplicit false

/-! # A positive scalar reserve for every large degree -/

namespace PrimeFactorUnimodality

open Real

noncomputable def classificationJ (v : Real) : Real := v - log (classificationH v) + 0.485

noncomputable def classificationDescentReserve (v : Real) : Real :=
  v - log (classificationH v) - log (classificationJ v) - 0.319 - 0.618 * classificationH v

theorem classificationH_derivative_bounds (v : Real) (hv : 10.545 <= v) :
    And (0 <= 1 - 1 / v)
      (And (1 - 1 / v <= 1) ((1 - 1 / v) / classificationH v <= 1 / 9)) := by
  have hvpos : 0 < v := by linarith
  have hH := (classificationH_bounds v hv).1
  have hinv : 1 / v <= (1 : Real) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) (by linarith : 1 <= v)
    simpa using h
  have hnum : 1 - 1 / v <= 1 := by linarith [one_div_pos.mpr hvpos]
  refine And.intro (by linarith) (And.intro hnum ?_)
  exact (div_le_div_of_nonneg_right hnum (by linarith : 0 <= classificationH v)).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 9) (by linarith))

theorem classificationJ_lower (v : Real) (hv : 10.545 <= v) :
    (8 : Real) < classificationJ v := by
  have hH := classificationH_bounds v hv
  have hlog := log_le_log (by linarith : 0 < classificationH v) hH.2.1.le
  unfold classificationJ classificationH at *
  linarith [hH.1]

theorem classificationJ_hasDerivAt (v : Real) (hv : 10.545 <= v) :
    HasDerivAt classificationJ (1 - (1 - 1 / v) / classificationH v) v := by
  have hH := (classificationH_bounds v hv).1
  unfold classificationJ
  convert! ((hasDerivAt_id' v).sub
    ((classificationH_hasDerivAt v (by linarith)).log (by linarith))).add_const 0.485 using 1
  <;> ring

theorem classificationDescentReserve_hasDerivAt (v : Real) (hv : 10.545 <= v) :
    HasDerivAt classificationDescentReserve
      (1 - (1 - 1 / v) / classificationH v -
        (1 - (1 - 1 / v) / classificationH v) / classificationJ v -
          0.618 * (1 - 1 / v)) v := by
  have hH := (classificationH_bounds v hv).1
  have hJ := classificationJ_lower v hv
  have hdH := classificationH_hasDerivAt v (by linarith)
  have hdJ := classificationJ_hasDerivAt v hv
  unfold classificationDescentReserve
  convert! ((((hasDerivAt_id' v).sub (hdH.log (by linarith))).sub
    (hdJ.log (by linarith))).sub_const 0.319).sub (hdH.const_mul 0.618) using 1
  <;> ring

theorem classificationDescentReserve_monotone :
    MonotoneOn classificationDescentReserve (Set.Ici 10.545) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 10.545)
  next =>
    intro v hv
    exact (classificationDescentReserve_hasDerivAt v hv).continuousAt.continuousWithinAt
  next =>
    intro v hv
    simp only [interior_Ici, Set.mem_Ioi] at hv
    exact (classificationDescentReserve_hasDerivAt v hv.le).differentiableAt.differentiableWithinAt
  next =>
    intro v hv
    simp only [interior_Ici, Set.mem_Ioi] at hv
    rw [(classificationDescentReserve_hasDerivAt v hv.le).deriv]
    have hHp := classificationH_derivative_bounds v hv.le
    have hH := (classificationH_bounds v hv.le).1
    have hJ := classificationJ_lower v hv.le
    have hfrac0 : 0 <= (1 - 1 / v) / classificationH v :=
      div_nonneg hHp.1 (by linarith)
    have hJp : 1 - (1 - 1 / v) / classificationH v <= 1 := by linarith
    have hJfrac : (1 - (1 - 1 / v) / classificationH v) / classificationJ v <= 1 / 8 :=
      (div_le_div_of_nonneg_right hJp (by linarith : 0 <= classificationJ v)).trans
        (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 8) hJ.le)
    nlinarith [hHp.2.1, hHp.2.2]

theorem classificationDescentReserve_pos (v : Real) (hv : 10.545 <= v) :
    0 < classificationDescentReserve v := by
  have hH0 : And (9.34 < classificationH 10.545) (classificationH 10.545 < 9.39) := by
    constructor
    next => exact (classificationH_bounds 10.545 (by norm_num)).1
    next =>
      unfold classificationH
      linarith [log_10545_bounds.1]
  have hLogH : And (2.23 < log (classificationH 10.545))
      (log (classificationH 10.545) < 2.24) :=
    And.intro
      (log_934_gt.trans (log_lt_log (by norm_num) hH0.1))
      ((log_lt_log (by linarith) hH0.2).trans log_939_lt)
  have hJ0 : classificationJ 10.545 < 8.8 := by
    unfold classificationJ
    linarith [hLogH.1]
  have hLogJ : log (classificationJ 10.545) < 2.175 :=
    (log_lt_log (by linarith [classificationJ_lower 10.545 (by norm_num)]) hJ0).trans log_88_lt
  have hbase : 0 < classificationDescentReserve 10.545 := by
    unfold classificationDescentReserve
    nlinarith [hLogH.2, hLogJ, hH0.2]
  exact hbase.trans_le
    (classificationDescentReserve_monotone
      (by change (10.545 : Real) <= 10.545; exact le_rfl) hv hv)

end PrimeFactorUnimodality
