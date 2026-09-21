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
        change a ≤ x at hx
        have hxpos : 0 < x := by linarith [ha, hx]
        exact ne_of_gt (by simpa only [id_eq] using hxpos))
    have hquot : ContinuousOn (fun x : Real => x / Real.log x) (Set.Ici a) := by
      convert continuousOn_id.div hlog (by
        intro x hx
        change a ≤ x at hx
        exact ne_of_gt (Real.log_pos (by linarith [ha, hx]))) using 1
      ext x
      rfl
    convert continuousOn_id.sub
      ((continuousOn_const : ContinuousOn (fun _ : Real => c) (Set.Ici a)).mul hquot) using 1
    · ext x
      change x - c * x / Real.log x = x - c * (x / Real.log x)
      ring
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici a)) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        have hxpos : 0 < x := by linarith [ha, hx']
        exact ne_of_gt (by simpa only [id_eq] using hxpos))
    have hquot : DifferentiableOn ℝ (fun x : Real => x / Real.log x)
        (interior (Set.Ici a)) := by
      convert differentiableOn_id.div hlog (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        exact ne_of_gt (Real.log_pos (lt_trans ha hx'))) using 1
      ext x
      rfl
    convert differentiableOn_id.sub
      ((differentiableOn_const c).mul hquot) using 1
    · ext x
      change x - c * x / Real.log x = x - c * (x / Real.log x)
      ring
  · intro x hx
    have hx' : a < x := by
      simpa only [interior_Ici, Set.mem_Ioi] using hx
    have hxpos : 0 < x := by linarith [ha, hx']
    have hlogpos : 0 < Real.log x :=
      Real.log_pos (lt_trans ha hx')
    have hlog : 1 ≤ Real.log x :=
      hloga.trans (Real.log_le_log (by linarith [ha]) hx'.le)
    have hderiv := (hasDerivAt_id x).sub
      ((hasDerivAt_const x c).mul
        ((hasDerivAt_id x).div
          (Real.hasDerivAt_log (ne_of_gt hxpos)) hlogpos.ne'))
    have hnonneg : 0 ≤ deriv (id - (fun _ : Real => c) * (id / Real.log)) x := by
      have hderiv_eq := hderiv.deriv
      simp only [id_eq] at hderiv_eq
      rw [hderiv_eq]
      field_simp [hlogpos.ne']
      have hmul : c * (Real.log x - 1) ≤ Real.log x - 1 := by
        exact (mul_le_mul_of_nonneg_right hc1 (by linarith)).trans_eq
          (one_mul (Real.log x - 1))
      nlinarith [sq_nonneg (Real.log x - 1), hmul]
    have hfun : id - (fun _ : Real => c) * (id / Real.log) =
        (fun y : Real => y - c * y / Real.log y) := by
      funext y
      change y - c * (y / Real.log y) = y - c * y / Real.log y
      ring
    rw [hfun] at hnonneg
    exact hnonneg

theorem id_add_mul_id_div_log_monotoneOn
    {a b : Real} (ha : 1 < a) (hloga : 1 ≤ Real.log a)
    (hb0 : -1 ≤ b) (hb1 : b ≤ 0) :
    MonotoneOn (fun x : Real => x + b * x / Real.log x) (Set.Ici a) := by
  have h := id_sub_mul_id_div_log_monotoneOn (a := a) (c := -b)
    ha hloga (by linarith) (by linarith)
  intro x hx y hy hxy
  have hxy' := h hx hy hxy
  convert hxy' using 1 <;> ring

theorem id_sub_mul_id_div_log_sq_monotoneOn
    {a c : Real} (ha : 1 < a) (hloga : 2 ≤ Real.log a)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    MonotoneOn (fun x : Real => x - c * x / Real.log x ^ 2) (Set.Ici a) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici a)
  · have hlog : ContinuousOn (fun y : Real => Real.log y) (Set.Ici a) := by
      exact continuousOn_id.log (by
        intro x hx
        change a ≤ x at hx
        have hxpos : 0 < x := by linarith [ha, hx]
        exact ne_of_gt (by simpa only [id_eq] using hxpos))
    have hquot : ContinuousOn (fun x : Real => x / Real.log x ^ 2) (Set.Ici a) := by
      convert continuousOn_id.div (hlog.pow 2) (by
        intro x hx
        change a ≤ x at hx
        exact pow_ne_zero 2
          (ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hx)))) using 1
      ext x
      rfl
    convert continuousOn_id.sub
      ((continuousOn_const : ContinuousOn (fun _ : Real => c) (Set.Ici a)).mul hquot) using 1
    · ext x
      change x - c * x / Real.log x ^ 2 = x - c * (x / Real.log x ^ 2)
      ring
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici a)) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        have hxpos : 0 < x := by linarith [ha, hx']
        exact ne_of_gt (by simpa only [id_eq] using hxpos))
    have hquot : DifferentiableOn ℝ (fun x : Real => x / Real.log x ^ 2)
        (interior (Set.Ici a)) := by
      convert differentiableOn_id.div (hlog.pow 2) (by
        intro x hx
        have hx' : a < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        exact pow_ne_zero 2
          (ne_of_gt (Real.log_pos (lt_trans ha hx')))) using 1
      ext x
      rfl
    convert differentiableOn_id.sub
      ((differentiableOn_const c).mul hquot) using 1
    · ext x
      change x - c * x / Real.log x ^ 2 = x - c * (x / Real.log x ^ 2)
      ring
  · intro x hx
    have hx' : a < x := by
      simpa only [interior_Ici, Set.mem_Ioi] using hx
    have hxpos : 0 < x := by linarith [ha, hx']
    have hlogpos : 0 < Real.log x :=
      Real.log_pos (lt_trans ha hx')
    have hlog : 2 ≤ Real.log x :=
      hloga.trans (Real.log_le_log (by linarith [ha]) hx'.le)
    have hderiv := (hasDerivAt_id x).sub
      ((hasDerivAt_const x c).mul
        ((hasDerivAt_id x).div
          ((Real.hasDerivAt_log (ne_of_gt hxpos)).pow 2)
          (pow_ne_zero 2 hlogpos.ne')))
    have hnonneg : 0 ≤ deriv (id - (fun _ : Real => c) * (id / Real.log ^ 2)) x := by
      have hderiv_eq := hderiv.deriv
      simp [id_eq, Pi.pow_apply] at hderiv_eq
      rw [hderiv_eq]
      field_simp [hlogpos.ne']
      have hmul : c * (Real.log x - 2) ≤ Real.log x - 2 := by
        exact (mul_le_mul_of_nonneg_right hc1 (by linarith)).trans_eq
          (one_mul (Real.log x - 2))
      nlinarith [sq_nonneg (Real.log x - 2), sq_nonneg (Real.log x), hmul]
    have hfun : id - (fun _ : Real => c) * (id / Real.log ^ 2) =
        (fun y : Real => y - c * y / Real.log y ^ 2) := by
      funext y
      change y - c * (y / Real.log y ^ 2) = y - c * y / Real.log y ^ 2
      ring
    rw [hfun] at hnonneg
    exact hnonneg

theorem id_add_mul_id_div_log_sq_monotoneOn
    {a b : Real} (ha : 1 < a) (hloga : 2 ≤ Real.log a)
    (hb0 : -1 ≤ b) (hb1 : b ≤ 0) :
    MonotoneOn (fun x : Real => x + b * x / Real.log x ^ 2) (Set.Ici a) := by
  have h := id_sub_mul_id_div_log_sq_monotoneOn (a := a) (c := -b)
    ha hloga (by linarith) (by linarith)
  intro x hx y hy hxy
  have hxy' := h hx hy hxy
  convert hxy' using 1 <;> ring

end

end PrimeFactorUnimodality
