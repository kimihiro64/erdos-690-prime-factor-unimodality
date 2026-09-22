import PrimeFactorUnimodality.Helpers.Analytic.XiCountingRectangle

/-! # The actual zero count as an xi half-contour argument

Xi conjugation and its functional equation reflect the left vertical
integral into the conjugate of the right, and the top-left horizontal
integral into minus the conjugate of the top-right. The bottom integral
has zero imaginary part. Consequently the proved full rectangle formula
reduces to `pi*N(T) = Im(Vright) - Im(HtopRight)`.

The integrals retain their orientations. The top must avoid zeros; the
regular-height limit module subsequently transfers continuous bounds to
every cutoff. No numerical zero-counting estimate is assumed here.
-/

namespace PrimeFactorUnimodality
noncomputable section
open Complex Filter MeasureTheory Set
open scoped ComplexConjugate Topology

/-- Xi's logarithmic derivative respects conjugation on the entire plane. -/
theorem logDeriv_riemannXi_conj (s : ℂ) :
    logDeriv riemannXi (conj s) = conj (logDeriv riemannXi s) := by
  have heq : (conj ∘ riemannXi ∘ conj) = riemannXi := by
    funext z
    simp only [Function.comp_apply, riemannXi_conj, conj_conj]
  have hd := (differentiable_riemannXi (conj s)).hasDerivAt.conj_conj
  simp only [conj_conj, heq] at hd
  have he : deriv riemannXi (conj s) = conj (deriv riemannXi s) := by
    rw [hd.deriv, conj_conj]
  simp only [logDeriv_apply, he, riemannXi_conj, map_div₀]

/-- Same-height reflection negates the conjugate logarithmic derivative. -/
theorem logDeriv_riemannXi_horizontal_reflection (x T : ℝ) :
    logDeriv riemannXi (((1 - x : ℝ) : ℂ) + T * I) =
      -conj (logDeriv riemannXi ((x : ℂ) + T * I)) := by
  have he : (((1 - x : ℝ) : ℂ) + T * I) = 1 - conj ((x : ℂ) + T * I) := by
    simp
    ring
  rw [he, logDeriv_riemannXi_one_sub, logDeriv_riemannXi_conj]

/-- The bottom, real-axis integral has zero imaginary part. -/
theorem im_HIntegral_logDeriv_xi_zero (a b : ℝ) :
    (HIntegral (logDeriv riemannXi) a b 0).im = 0 := by
  have he : conj (HIntegral (logDeriv riemannXi) a b 0) =
      HIntegral (logDeriv riemannXi) a b 0 := by
    unfold HIntegral
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [ofReal_zero, zero_mul, add_zero, ← logDeriv_riemannXi_conj, conj_ofReal]
  have h := congrArg Complex.im he
  simp only [conj_im] at h
  linarith

/-- The left vertical integral is the conjugate of the right vertical integral. -/
theorem VIntegral_logDeriv_xi_reflection (σ T : ℝ) :
    VIntegral (logDeriv riemannXi) (1 - σ) 0 T =
      conj (VIntegral (logDeriv riemannXi) σ 0 T) := by
  unfold VIntegral
  simp only [logDeriv_riemannXi_horizontal_reflection, smul_eq_mul, map_mul, conj_I,
    intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]
  ring

/-- The top-left half is minus the conjugate of the top-right half. -/
theorem HIntegral_logDeriv_xi_left_reflection (σ T : ℝ) :
    HIntegral (logDeriv riemannXi) (1 - σ) (1 / 2) T =
      -conj (HIntegral (logDeriv riemannXi) (1 / 2) σ T) := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := (1 / 2 : ℝ)) (b := σ)
    (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + T * I)) 1
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  unfold HIntegral
  rw [← h]
  simp only [logDeriv_riemannXi_horizontal_reflection, intervalIntegral.integral_neg,
    intervalIntegral.intervalIntegral_conj]

/-- A horizontal line avoiding xi zeros has continuous logarithmic derivative. -/
theorem continuous_logDeriv_xi_horizontal {T : ℝ}
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Continuous (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + T * I)) := by
  have hdc : Continuous (deriv riemannXi) :=
    continuous_iff_continuousAt.mpr
      (fun z => (differentiable_riemannXi.analyticAt z).deriv.continuousAt)
  have hc : Continuous (fun x : ℝ => (x : ℂ) + T * I) := by fun_prop
  exact (hdc.comp hc).div (differentiable_riemannXi.continuous.comp hc)
    (fun x => htop _ (by simp))

/-- The full top integral is twice the imaginary part of its right half. -/
theorem HIntegral_logDeriv_xi_eq_sub_conj {σ T : ℝ}
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HIntegral (logDeriv riemannXi) (1 - σ) σ T =
      HIntegral (logDeriv riemannXi) (1 / 2) σ T -
        conj (HIntegral (logDeriv riemannXi) (1 / 2) σ T) := by
  have hc := continuous_logDeriv_xi_horizontal htop
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (1 - σ) (1 / 2)) (hc.intervalIntegrable (1 / 2) σ)
  change HIntegral (logDeriv riemannXi) (1 - σ) (1 / 2) T +
    HIntegral (logDeriv riemannXi) (1 / 2) σ T =
      HIntegral (logDeriv riemannXi) (1 - σ) σ T at hs
  rw [← hs, HIntegral_logDeriv_xi_left_reflection]
  ring

/-- The actual count equals the correctly oriented half-contour argument divided by pi. -/
theorem pi_mul_zeta_N_eq_xi_half_contour {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 ≤ T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Real.pi * riemannZeta.N T =
      (VIntegral (logDeriv riemannXi) σ 0 T).im -
        (HIntegral (logDeriv riemannXi) (1 / 2) σ T).im := by
  have hc := rectangleIntegral_logDeriv_xi_eq_zeta_N hσ hT htop
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have he : RectangleIntegral (logDeriv riemannXi)
      ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I) =
        (2 * Real.pi * I) * (riemannZeta.N T : ℂ) := by
    simp only [RectangleIntegral', smul_eq_mul, one_div] at hc
    exact (inv_mul_eq_iff_eq_mul₀ hpi).mp hc
  have hi := congrArg Complex.im he
  simp only [RectangleIntegral, ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im,
    I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
    sub_im, im_HIntegral_logDeriv_xi_zero, HIntegral_logDeriv_xi_eq_sub_conj htop,
    VIntegral_logDeriv_xi_reflection, conj_im] at hi
  norm_num at hi
  nlinarith [hi]

end
end PrimeFactorUnimodality
