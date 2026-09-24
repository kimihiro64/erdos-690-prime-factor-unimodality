import PrimeFactorUnimodality.Helpers.Analytic.PlattContourSharedEdgeBound
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.HorizontalIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.ShiftNorm
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.PolynomialDecay

set_option autoImplicit false

/-! # Vanishing connecting edges for the leftward Gamma contour

Far along either edge the imaginary part of the Gamma argument has absolute
value at least one. Recurrence moves its real part into a positive strip,
where the Euler-integral bound applies. The shared Gaussian majorant then
proves both edge limits, even though the full rectangle contains poles.
-/

open Filter Set
open scoped Topology

namespace PrimeFactorUnimodality

/-- The finite uniform coefficient for this upward displacement. -/
noncomputable def plattLeftEdgeConstant (m k : ℕ) (t₀ h u : ℝ) : ℝ :=
  plattContourEdgeConstant k (2 * (m : ℝ) + 3 / 2)
    (max (Real.Gamma (3 / 2)) (Real.Gamma ((m : ℝ) + 9 / 4))) t₀ h u

/-- Uniform decay on the full left-shift edge once its real coordinate is sufficiently large. -/
theorem norm_plattContourIntegrand_left_edge_le (m k : ℕ) (t₀ u : ℝ)
    {h v w : ℝ} (hh : 0 < h) (hv : 1 ≤ |v|) (hv' : Real.pi * h ^ 2 ≤ |v|)
    (hvΓ : |t₀| + 2 ≤ |v|) (hw : w ∈ Icc 0 (2 * (m : ℝ) + 3 / 2)) :
    ‖plattContourIntegrand k t₀ h u ((v : ℂ) + (w : ℂ) * Complex.I)‖ ≤
      plattLeftEdgeConstant m k t₀ h u *
        (|v| ^ k * Real.exp (-(1 / (4 * h ^ 2)) * |v| ^ 2)) := by
  have him : 1 ≤ |(v + t₀) / 2| := by
    have ht := abs_sub (v + t₀) t₀
    rw [add_sub_cancel_right] at ht
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hg := Complex.norm_Gamma_le_max_of_shifted_re_mem_Icc (m + 2)
    (a := 3 / 2) (b := (m : ℝ) + 9 / 4) (by norm_num) (by positivity)
    (z := ((1 / 4 - w / 2 : ℝ) : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)
    (by simpa using him) (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Nat.cast_add, Nat.cast_ofNat, Set.mem_Icc]
      constructor <;> linarith [hw.1, hw.2])
  exact norm_plattContourIntegrand_edge_le k t₀ u hh (by positivity) hv hv'
    (by simpa only [abs_of_nonneg hw.1] using hw.2) hg

/-- Each connecting integral vanishes, for either sign of the real coordinate. -/
theorem tendsto_integral_plattContour_left_edge_zero (m k : ℕ) (t₀ u : ℝ)
    {h ε : ℝ} (hh : 0 < h) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..(2 * (m : ℝ) + 3 / 2),
      plattContourIntegrand k t₀ h u (((ε * T : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  apply Complex.tendsto_integral_vertical_zero_of_bound
    (B := fun T => plattLeftEdgeConstant m k t₀ h u *
      (T ^ k * Real.exp (-(1 / (4 * h ^ 2)) * T ^ 2)))
    (by simpa using (Real.tendsto_pow_mul_exp_neg_mul_sq k
      (by positivity : 0 < 1 / (4 * h ^ 2))).const_mul (plattLeftEdgeConstant m k t₀ h u))
  filter_upwards [eventually_ge_atTop (max (Real.pi * h ^ 2) (|t₀| + 2))] with T hT
  intro y hy
  have hTΓ : |t₀| + 2 ≤ T := (le_max_right _ _).trans hT
  have hT₁ : 1 ≤ T := by linarith [abs_nonneg t₀]
  have hT₂ : Real.pi * h ^ 2 ≤ T := (le_max_left _ _).trans hT
  have habs : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
  have hy' : y ∈ Icc 0 (2 * (m : ℝ) + 3 / 2) := by
    simpa only [uIcc_of_le (by positivity : 0 ≤ 2 * (m : ℝ) + 3 / 2)] using hy
  simpa only [habs] using norm_plattContourIntegrand_left_edge_le m k t₀ u hh
    (v := ε * T) (by simpa only [habs] using hT₁)
    (by simpa only [habs] using hT₂) (by simpa only [habs] using hTΓ) hy'

end PrimeFactorUnimodality
