import PrimeFactorUnimodality.Helpers.Analytic.PlattContourLeftEdge
import PrimeFactorUnimodality.Helpers.Analytic.PlattContourRectangle
import PrimeFactorUnimodality.Helpers.Analytic.PlattContourRightShift

set_option autoImplicit false

/-! # The leftward Fourier contour shift with all crossed residues

The finite rectangle identity and both vanishing edges identify the actual
Fourier transform with its upward displacement plus the explicit residues.
The corrected negative-line Gamma bound then gives negative-frequency decay,
retaining every residue and the first-shift correction factor.
-/

open MeasureTheory Filter
open scoped Topology FourierTransform

namespace PrimeFactorUnimodality

/-- The unnormalized rectangle identity in the coordinates of the Fourier integral. -/
theorem plattContour_left_rectangle_identity (m k : ℕ) {t₀ T : ℝ}
    (hT : |t₀| < T) (h u : ℝ) :
    (∫ v in -T..T, plattContourIntegrand k t₀ h u (v : ℂ)) -
      (∫ v in -T..T, plattContourIntegrand k t₀ h u
        ((v : ℂ) + (((2 * (m : ℝ) + 3 / 2 : ℝ)) : ℂ) * Complex.I)) +
      Complex.I * (∫ y in (0 : ℝ)..(2 * (m : ℝ) + 3 / 2),
        plattContourIntegrand k t₀ h u ((T : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in (0 : ℝ)..(2 * (m : ℝ) + 3 / 2),
        plattContourIntegrand k t₀ h u ((-T : ℝ) + (y : ℂ) * Complex.I)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ n ∈ Finset.range (m + 1), plattContourResidueValue n k t₀ h u := by
  have hc : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have he := congrArg (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * z)
    (rectangleIntegral_plattContourIntegrand_eq_sum m k hT h u)
  simp only [RectangleIntegral', smul_eq_mul, one_div] at he
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at he
  simpa [RectangleIntegral, HIntegral, VIntegral] using he

/-- The actual Fourier transform equals the displaced integral plus every crossed residue. -/
theorem fourier_plattWindowKernel_eq_left_integral_add_residues (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    𝓕 (plattWindowKernel k t₀ h) u =
      (∫ v : ℝ, plattContourIntegrand k t₀ h u
        ((v : ℂ) + (((2 * (m : ℝ) + 3 / 2 : ℝ)) : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ n ∈ Finset.range (m + 1), plattContourResidueValue n k t₀ h u := by
  have hright : Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..(2 * (m : ℝ) + 3 / 2),
      plattContourIntegrand k t₀ h u ((T : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
    simpa using tendsto_integral_plattContour_left_edge_zero m k t₀ u hh (ε := 1) (by norm_num)
  have hleft : Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..(2 * (m : ℝ) + 3 / 2),
      plattContourIntegrand k t₀ h u ((-T : ℝ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
    simpa using tendsto_integral_plattContour_left_edge_zero m k t₀ u hh (ε := -1) (by norm_num)
  have hbottom := intervalIntegral_tendsto_integral
    (integrable_plattContourIntegrand_real k t₀ u hh) tendsto_neg_atTop_atBot tendsto_id
  have htop := intervalIntegral_tendsto_integral
    (integrable_plattContourIntegrand_left m k hm ht₀ hh u) tendsto_neg_atTop_atBot tendsto_id
  have hlimit := ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub
    (hleft.const_mul Complex.I)
  have he : ∀ᶠ T in atTop, (∫ v in -T..T, plattContourIntegrand k t₀ h u (v : ℂ)) -
      (∫ v in -T..T, plattContourIntegrand k t₀ h u
        ((v : ℂ) + (((2 * (m : ℝ) + 3 / 2 : ℝ)) : ℂ) * Complex.I)) +
      Complex.I * (∫ y in (0 : ℝ)..(2 * (m : ℝ) + 3 / 2),
        plattContourIntegrand k t₀ h u ((T : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in (0 : ℝ)..(2 * (m : ℝ) + 3 / 2),
        plattContourIntegrand k t₀ h u ((-T : ℝ) + (y : ℂ) * Complex.I)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ n ∈ Finset.range (m + 1), plattContourResidueValue n k t₀ h u := by
    filter_upwards [eventually_gt_atTop |t₀|] with T hT
    exact plattContour_left_rectangle_identity m k hT h u
  have hid := tendsto_nhds_unique hlimit
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))
  simp only [mul_zero, add_zero, sub_zero] at hid
  rw [fourier_plattWindowKernel_eq_integral]
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hid

/-- Negative-frequency control of the genuine transform with an explicit residue sum. -/
theorem norm_fourier_plattWindowKernel_le_left_shift (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
        2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2)) *
        (plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h) +
      2 * Real.pi * ∑ n ∈ Finset.range (m + 1), ‖plattContourResidueValue n k t₀ h u‖ := by
  rw [fourier_plattWindowKernel_eq_left_integral_add_residues m k hm ht₀ hh u]
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_integral_plattContourIntegrand_left_le m k hm ht₀ hh u)
  have hc : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_mul, hc]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

end PrimeFactorUnimodality
