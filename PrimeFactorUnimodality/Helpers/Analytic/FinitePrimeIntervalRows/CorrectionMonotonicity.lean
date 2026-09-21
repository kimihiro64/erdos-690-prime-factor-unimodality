import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting

set_option autoImplicit false

/-! Monotonicity of the logarithmic correction functions used by Table 6.6. -/

namespace PrimeFactorUnimodality

noncomputable section

theorem id_sub_mul_id_div_log_monotoneOn
    {a c : Real} (ha : 1 < a) (hloga : 1 ≤ Real.log a)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    MonotoneOn (fun x : Real => x - c * x / Real.log x) (Set.Ici a) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici a)
  · have hlog : ContinuousOn (fun y : Real => Real.log y) (Set.Ici a) := by
      exact continuousOn_id.log (by
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le ha hx))
    exact continuousOn_id.sub
      (continuousOn_const.mul (continuousOn_id.div hlog (by
        intro x hx
        exact ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hx)))))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici a)) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        exact ne_of_gt (by linarith [ha, hx']))
    exact differentiableOn_id.sub
      (differentiableOn_const.mul (differentiableOn_id.div hlog (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        exact pow_ne_zero 1
          (ne_of_gt (Real.log_pos (lt_trans ha hx'))))))
  · intro x hx
    have hx' : a < x := by
      simpa only [interior_Ici, Set.mem_Ioi] using hx
    have hxpos : 0 < x := by linarith [ha, hx']
    have hlogpos : 0 < Real.log x :=
      Real.log_pos (lt_trans ha hx')
    have hlog : 1 ≤ Real.log x :=
      hloga.trans (Real.log_le_log (by linarith [ha, hx']) hx'.le)
    have hquot := deriv_log_power_kernel (n := 0) (by linarith [ha, hx'])
    have hderiv := (hasDerivAt_id x).sub
      ((hasDerivAt_const x c).mul
        ((hasDerivAt_id x).div
          (Real.hasDerivAt_log (ne_of_gt hxpos)) hlogpos.ne'))
    change 0 ≤ deriv (fun y : Real => y - c * y / Real.log y) x
    rw [hderiv.deriv, hquot]
    field_simp [hlogpos.ne']
    have hmul : c * (Real.log x - 1) ≤ Real.log x - 1 := by
      exact (mul_le_mul_of_nonneg_right hc1 (by linarith)).trans_eq
        (one_mul (Real.log x - 1))
    nlinarith [sq_nonneg (Real.log x - 1), hmul]

theorem id_add_mul_id_div_log_monotoneOn
    {a b : Real} (ha : 1 < a) (hloga : 1 ≤ Real.log a)
    (hb0 : -1 ≤ b) (hb1 : b ≤ 0) :
    MonotoneOn (fun x : Real => x + b * x / Real.log x) (Set.Ici a) := by
  have h := id_sub_mul_id_div_log_monotoneOn (a := a) (c := -b)
    ha hloga (by linarith) (by linarith)
  intro x hx y hy hxy
  have hxy' := h hx hy hxy
  simpa [sub_eq_add_neg, neg_mul] using hxy'

theorem id_sub_mul_id_div_log_sq_monotoneOn
    {a c : Real} (ha : 1 < a) (hloga : 2 ≤ Real.log a)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    MonotoneOn (fun x : Real => x - c * x / Real.log x ^ 2) (Set.Ici a) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici a)
  · have hlog : ContinuousOn (fun y : Real => Real.log y) (Set.Ici a) := by
      exact continuousOn_id.log (by
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le ha hx))
    exact continuousOn_id.sub
      (continuousOn_const.mul (continuousOn_id.div (hlog.pow 2) (by
        intro x hx
        exact pow_ne_zero 2
          (ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hx))))))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici a)) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        exact ne_of_gt (by linarith [ha, hx']))
    exact differentiableOn_id.sub
      (differentiableOn_const.mul (differentiableOn_id.div (hlog.pow 2) (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        exact pow_ne_zero 2
          (ne_of_gt (Real.log_pos (lt_trans ha hx'))))))
  · intro x hx
    have hx' : a < x := by
      simpa only [interior_Ici, Set.mem_Ioi] using hx
    have hxpos : 0 < x := by linarith [ha, hx']
    have hlogpos : 0 < Real.log x :=
      Real.log_pos (lt_trans ha hx')
    have hlog : 2 ≤ Real.log x :=
      hloga.trans (Real.log_le_log (by linarith [ha, hx']) hx'.le)
    have hquot := deriv_log_power_kernel (n := 1) (by linarith [ha, hx'])
    have hderiv := (hasDerivAt_id x).sub
      ((hasDerivAt_const x c).mul
        ((hasDerivAt_id x).div
          ((Real.hasDerivAt_log (ne_of_gt hxpos)).pow 2)
          (pow_ne_zero 2 hlogpos.ne')))
    change 0 ≤ deriv (fun y : Real => y - c * y / Real.log y ^ 2) x
    rw [hderiv.deriv, hquot]
    field_simp [hlogpos.ne']
    have hmul : c * (Real.log x - 2) ≤ Real.log x - 2 := by
      exact (mul_le_mul_of_nonneg_right hc1 (by linarith)).trans_eq
        (one_mul (Real.log x - 2))
    nlinarith [sq_nonneg (Real.log x - 2), sq_nonneg (Real.log x), hmul]

theorem id_add_mul_id_div_log_sq_monotoneOn
    {a b : Real} (ha : 1 < a) (hloga : 2 ≤ Real.log a)
    (hb0 : -1 ≤ b) (hb1 : b ≤ 0) :
    MonotoneOn (fun x : Real => x + b * x / Real.log x ^ 2) (Set.Ici a) := by
  have h := id_sub_mul_id_div_log_sq_monotoneOn (a := a) (c := -b)
    ha hloga (by linarith) (by linarith)
  intro x hx y hy hxy
  have hxy' := h hx hy hxy
  simpa [sub_eq_add_neg, neg_mul] using hxy'

end

end PrimeFactorUnimodality
