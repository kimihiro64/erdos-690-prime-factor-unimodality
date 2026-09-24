import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaContourEdge
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaRectangle

set_option autoImplicit false

/-! # The actual zeta-window Fourier transform as a Dirichlet series

The finite residue identity, vanishing edges and absolute convergence of
both horizontal integrals prove the contour shift. The justified Dirichlet
interchange then gives the series identity with its full complex pole
correction. This is the analytic connection required by Platt's Lemma 3.2.
-/

open MeasureTheory Filter
open scoped Topology FourierTransform

namespace PrimeFactorUnimodality

/-- The counterclockwise finite rectangle has lower integral minus upper integral. -/
theorem plattZetaContour_rectangle_identity (m k : ℕ) (hm : 1 ≤ m) {t₀ T : ℝ}
    (hT : |t₀| < T) (h x : ℝ) :
    (∫ v in -T..T, plattZetaContourIntegrand k t₀ h x
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) -
      (∫ v in -T..T, plattZetaContourIntegrand k t₀ h x (v : ℂ)) +
      Complex.I * (∫ y in (-plattRightShift m)..(0 : ℝ),
        plattZetaContourIntegrand k t₀ h x ((T : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in (-plattRightShift m)..(0 : ℝ),
        plattZetaContourIntegrand k t₀ h x ((-T : ℝ) + (y : ℂ) * Complex.I)) =
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x := by
  have hc : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have he := congrArg (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * z)
    (rectangleIntegral_plattZetaContourIntegrand_eq m k hm hT h x)
  simp only [RectangleIntegral', smul_eq_mul, one_div] at he
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at he
  simpa [RectangleIntegral, HIntegral, VIntegral] using he

/-- The true critical-line transform equals the displaced integral minus the crossed residue. -/
theorem fourier_plattZetaWindow_eq_right_integral_sub_residue (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    𝓕 (plattZetaWindow k t₀ h) x =
      (∫ v : ℝ, plattZetaContourIntegrand k t₀ h x
        ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) -
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x := by
  have hrightDown := tendsto_integral_plattZetaContour_right_edge_zero m k t₀ x hh
    (ε := 1) (by norm_num)
  have hleftDown := tendsto_integral_plattZetaContour_right_edge_zero m k t₀ x hh
    (ε := -1) (by norm_num)
  have hright : Tendsto (fun T : ℝ => ∫ y in (-plattRightShift m)..(0 : ℝ),
      plattZetaContourIntegrand k t₀ h x ((T : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_symm (-plattRightShift m) 0, one_mul, neg_zero,
      neg_neg] using
      hrightDown.neg
  have hleft : Tendsto (fun T : ℝ => ∫ y in (-plattRightShift m)..(0 : ℝ),
      plattZetaContourIntegrand k t₀ h x ((-T : ℝ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_symm (-plattRightShift m) 0, neg_one_mul, neg_zero,
      neg_neg] using
      hleftDown.neg
  have hbottom := intervalIntegral_tendsto_integral
    (integrable_plattZetaContourIntegrand_right m k hm ht₀ hh x) tendsto_neg_atTop_atBot tendsto_id
  have htop := intervalIntegral_tendsto_integral
    (integrable_plattZetaContourIntegrand_real k t₀ x hh) tendsto_neg_atTop_atBot tendsto_id
  have hlimit := ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub
    (hleft.const_mul Complex.I)
  have he : ∀ᶠ T in atTop, (∫ v in -T..T, plattZetaContourIntegrand k t₀ h x
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) -
      (∫ v in -T..T, plattZetaContourIntegrand k t₀ h x (v : ℂ)) +
      Complex.I * (∫ y in (-plattRightShift m)..(0 : ℝ),
        plattZetaContourIntegrand k t₀ h x ((T : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in (-plattRightShift m)..(0 : ℝ),
        plattZetaContourIntegrand k t₀ h x ((-T : ℝ) + (y : ℂ) * Complex.I)) =
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x := by
    filter_upwards [eventually_gt_atTop |t₀|] with T hT
    exact plattZetaContour_rectangle_identity m k hm hT h x
  have hid := tendsto_nhds_unique hlimit
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))
  simp only [mul_zero, add_zero, sub_zero] at hid
  rw [fourier_plattZetaWindow_eq_integral]
  linear_combination -hid

/-- The complete series identity for the actual zeta transform, including the pole correction. -/
theorem fourier_plattZetaWindow_eq_series_sub_residue (k : ℕ)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    𝓕 (plattZetaWindow k t₀ h) x = plattDirichletSeries k t₀ h x -
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x := by
  rw [fourier_plattZetaWindow_eq_right_integral_sub_residue 1 k (by omega) ht₀ hh x,
    integral_plattZetaContourIntegrand_right_eq_series 1 k (by omega) ht₀ hh x]

/-- Dirichlet truncation bounds the actual zeta transform with its pole correction. -/
theorem norm_fourier_plattZetaWindow_sub_prefix_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) {J : ℕ} (hJ : 0 < J) :
    ‖𝓕 (plattZetaWindow k t₀ h) x -
        ((∑ n ∈ Finset.range J, plattDirichletTerm k t₀ h x (n + 1)) -
          (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x)‖ ≤
      plattDirichletTailBound m k t₀ h x J := by
  rw [fourier_plattZetaWindow_eq_series_sub_residue k ht₀ hh x, sub_sub_sub_cancel_right]
  exact norm_plattDirichletSeries_sub_prefix_le m k hm ht₀ hh x hJ

end PrimeFactorUnimodality
