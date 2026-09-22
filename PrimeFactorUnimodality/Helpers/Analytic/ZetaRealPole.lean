import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.ZetaTrigonometric
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

set_option autoImplicit false

/-! # Explicit real-axis pole bounds

The fractional-part Abel integral gives `Re ζ(σ) ≥ 1/(σ-1)` and
`Re (-ζ'/ζ)(σ) ≤ 1/(σ-1) + 1` for every real `σ > 1`.
The second estimate retains the unit coefficient of the pole, which is
essential in the trigonometric zero-free-region argument.

We use the Abel kernel and dominated differentiation primitives from
`PrimeNumberTheoremAnd` at the pinned revision recorded in `lake-manifest.json`.
Those primitives are by Matteo Cipollina, under Apache-2.0; no numerical
prime-number estimate is imported here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

private theorem zetaAbelFractKernel_ofReal {σ u : ℝ} (hu : 0 ≤ u) :
    zetaAbelFractKernel (σ : ℂ) u = ((Int.fract u * u ^ (-σ - 1) : ℝ) : ℂ) := by
  simp only [zetaAbelFractKernel, ofReal_mul]
  rw [show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow hu]

/-- The Abel fractional-part integral is bounded by its elementary power majorant. -/
theorem norm_zetaAbelIntegral_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ 1 / s.re := by
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one
  calc
    _ ≤ ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_zetaAbelFractKernel_le u hu.le s
    _ = 1 / s.re := integral_Ioi_rpow_neg_re_sub_one hs

/-- Differentiation of the Abel integral, retaining the signed logarithmic kernel. -/
theorem hasDerivAt_zetaAbelIntegral {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u)
      (∫ u in Ioi (1 : ℝ), -(Real.log u : ℂ) * zetaAbelFractKernel s u) s := by
  let ε : ℝ := s.re / 2
  have hε : 0 < ε := half_pos hs
  apply ZetaAbelFractKernel.hasDerivAt_integral_param_dominated_Ioi
    zetaAbelFractKernel (fun z u => -(Real.log u : ℂ) * zetaAbelFractKernel z u)
    s ε hε (ZetaAbelFractKernel.eventually_aestronglyMeasurable_param s)
    (ZetaAbelFractKernel.integrableOn_Ioi s hs)
    (ZetaAbelFractKernel.aestronglyMeasurable_param_deriv s)
    (fun u => (2 / ε) * u ^ (-1 - ε / 2))
  · exact (integrableOn_Ioi_rpow_of_lt (by linarith [hε]) zero_lt_one).const_mul (2 / ε)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    have hzdist : ‖z - s‖ < ε := by simpa [dist_eq_norm] using hz
    have hre : ε ≤ z.re := by
      have habs := Complex.abs_re_le_norm (z - s)
      simp only [sub_re] at habs
      have hl := neg_abs_le (z.re - s.re)
      dsimp [ε] at *
      linarith
    exact (ZetaAbelFractKernel.kernel_deriv_norm_bound_on_ball ε u hu z hre).trans
      (Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hε hu)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    exact ZetaAbelFractKernel.hasDerivAt_in_param u hu z

private theorem zetaAbel_derivative_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => -(Real.log u : ℂ) * zetaAbelFractKernel (σ : ℂ) u)
      (Ioi (1 : ℝ)) volume := by
  apply Integrable.mono'
    ((integrableOn_Ioi_rpow_of_lt (by linarith : -1 - σ / 2 < -1) zero_lt_one).const_mul (2 / σ))
    (ZetaAbelFractKernel.aestronglyMeasurable_param_deriv (σ : ℂ))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (ZetaAbelFractKernel.kernel_deriv_norm_bound_on_ball σ u hu (σ : ℂ) le_rfl).trans
    (Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hσ hu)

/-- The derivative of the real Abel integral is nonpositive, with no absolute-value loss. -/
theorem re_zetaAbelIntegral_derivative_nonpos {σ : ℝ} (hσ : 0 < σ) :
    (∫ u in Ioi (1 : ℝ), -(Real.log u : ℂ) * zetaAbelFractKernel (σ : ℂ) u).re ≤ 0 := by
  have heq : (∫ u in Ioi (1 : ℝ), -(Real.log u : ℂ) * zetaAbelFractKernel (σ : ℂ) u).re =
      ∫ u in Ioi (1 : ℝ), (-(Real.log u : ℂ) * zetaAbelFractKernel (σ : ℂ) u).re :=
    (integral_re (zetaAbel_derivative_integrable hσ)).symm
  rw [heq]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [zetaAbelFractKernel_ofReal hu0.le]
  simp only [neg_mul, ofReal_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, zero_mul,
    sub_zero]
  exact neg_nonpos.mpr (mul_nonneg (Real.log_pos hu).le
    (mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg hu0.le _)))

/-- The real zeta value dominates the pole itself. -/
theorem one_div_sub_one_le_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hb := norm_zetaAbelIntegral_le (s := (σ : ℂ)) hσ0
  have hr := (Complex.re_le_norm (∫ u in Ioi (1 : ℝ),
    zetaAbelFractKernel (σ : ℂ) u)).trans hb
  simp only [ofReal_re] at hr
  rw [riemannZeta_abel_integral (σ : ℂ) hσ, zetaAbelContinuationFormula]
  have hcast : 1 / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  simp only [sub_re, add_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
  have hmul := mul_le_mul_of_nonneg_left hr hσ0.le
  have hcancel : σ * (1 / σ) = 1 := by field_simp
  rw [hcancel] at hmul
  linarith

/-- The norm of the real zeta value is at most one plus the pole. -/
theorem norm_riemannZeta_real_le_pole_add_one {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ ≤ 1 / (σ - 1) + 1 := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hnonneg : 0 ≤ (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (σ : ℂ) u).re := by
    have heq : (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (σ : ℂ) u).re =
        ∫ u in Ioi (1 : ℝ), (zetaAbelFractKernel (σ : ℂ) u).re :=
      (integral_re (ZetaAbelFractKernel.integrableOn_Ioi (σ : ℂ) hσ0)).symm
    rw [heq]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [zetaAbelFractKernel_ofReal (zero_lt_one.trans hu).le, ofReal_re]
    exact mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg (zero_lt_one.trans hu).le _)
  have him : (riemannZeta (σ : ℂ)).im = 0 := by
    have h := congrArg Complex.im (riemannZeta_conj (σ : ℂ))
    simp only [conj_ofReal, conj_im] at h
    linarith
  have hpos : 0 < (riemannZeta (σ : ℂ)).re :=
    (by positivity : 0 < 1 / (σ - 1)).trans_le (one_div_sub_one_le_re_riemannZeta hσ)
  have hz : riemannZeta (σ : ℂ) = ((riemannZeta (σ : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  calc
    ‖riemannZeta (σ : ℂ)‖ = (riemannZeta (σ : ℂ)).re := by
      conv_lhs => rw [hz, norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    _ ≤ 1 / (σ - 1) + 1 := by
      rw [riemannZeta_abel_integral (σ : ℂ) hσ, zetaAbelContinuationFormula]
      have hcast : 1 / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast]
      simp only [sub_re, add_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
      nlinarith

/-- A signed derivative bound: the logarithmic integral has the helpful sign. -/
theorem neg_re_deriv_riemannZeta_le {σ : ℝ} (hσ : 1 < σ) :
    -(deriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) ^ 2 + 1 / σ := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  let F : ℂ → ℂ := fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u
  let D : ℂ := ∫ u in Ioi (1 : ℝ), -(Real.log u : ℂ) * zetaAbelFractKernel (σ : ℂ) u
  have hne : (σ : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by intro h; have := congrArg Complex.re h; simp at this; linarith)
  have hd := ((hasDerivAt_const (σ : ℂ) (1 : ℂ)).add
    ((hasDerivAt_const (σ : ℂ) (1 : ℂ)).div
      ((hasDerivAt_id (σ : ℂ)).sub_const 1) hne)).sub
    ((hasDerivAt_id (σ : ℂ)).mul (hasDerivAt_zetaAbelIntegral hσ0))
  have heq : (fun z : ℂ => 1 + 1 / (z - 1) - z * F z) =ᶠ[𝓝 (σ : ℂ)] riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hσ] with z hz
    exact (riemannZeta_abel_integral z hz).symm
  have hderiv : deriv riemannZeta (σ : ℂ) =
      -(1 / ((σ : ℂ) - 1) ^ 2) - F (σ : ℂ) - (σ : ℂ) * D := by
    rw [← heq.deriv_eq]
    have hdeq := hd.deriv
    change deriv (fun z : ℂ => 1 + 1 / (z - 1) - z * F z) (σ : ℂ) = _ at hdeq
    rw [hdeq]
    simp only [id_eq, zero_mul, zero_sub, one_mul, zero_add]
    dsimp [F, D]
    ring
  rw [hderiv]
  have hcast : (1 / ((σ : ℂ) - 1) ^ 2) = ((1 / (σ - 1) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  simp only [sub_re, neg_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
  have hD : D.re ≤ 0 := re_zetaAbelIntegral_derivative_nonpos hσ0
  have hF : (F (σ : ℂ)).re ≤ 1 / σ :=
    (Complex.re_le_norm _).trans (norm_zetaAbelIntegral_le hσ0)
  nlinarith

/-- Explicit pole estimate for the logarithmic derivative on the real axis. -/
theorem re_neg_logDeriv_riemannZeta_le_pole_add_one {σ : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hp : 0 < σ - 1 := sub_pos.mpr hσ
  have hlower := one_div_sub_one_le_re_riemannZeta hσ
  have hzpos : 0 < (riemannZeta (σ : ℂ)).re := (by positivity : 0 < 1 / (σ - 1)).trans_le hlower
  have him : (riemannZeta (σ : ℂ)).im = 0 := by
    have h := congrArg Complex.im (riemannZeta_conj (σ : ℂ))
    simp only [conj_ofReal, conj_im] at h
    linarith
  have hre : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
      -(deriv riemannZeta (σ : ℂ)).re / (riemannZeta (σ : ℂ)).re := by
    rw [Complex.div_re, normSq_apply, him]
    simp only [neg_re, mul_zero, add_zero]
    field_simp
    ring
  rw [hre]
  calc
    _ ≤ (1 / (σ - 1) ^ 2 + 1 / σ) / (riemannZeta (σ : ℂ)).re :=
      div_le_div_of_nonneg_right (neg_re_deriv_riemannZeta_le hσ) hzpos.le
    _ ≤ (1 / (σ - 1) ^ 2 + 1 / σ) / (1 / (σ - 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlower
    _ = 1 / (σ - 1) + (σ - 1) / σ := by field_simp
    _ ≤ 1 / (σ - 1) + 1 := by
      apply add_le_add_right
      exact (div_le_one hσ0).mpr (by linarith)

/-- The real-axis estimate controls the logarithmic derivative throughout `Re(s) > 1`. -/
theorem norm_logDeriv_riemannZeta_le_pole_add_one {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + 1 := by
  simpa only [neg_div, norm_neg] using
    (norm_neg_logDeriv_riemannZeta_le_real hs).trans
      (re_neg_logDeriv_riemannZeta_le_pole_add_one hs)

end

end PrimeFactorUnimodality
