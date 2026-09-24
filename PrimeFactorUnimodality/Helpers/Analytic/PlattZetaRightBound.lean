import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaFourier

set_option autoImplicit false

/-! # The positive-frequency bound for the genuine zeta transform

Absolute convergence of zeta on the displaced line bounds it by its real-axis
value. The pi phase has constant norm there. Combining these factors with
the Gamma integral-norm estimate bounds the actual Dirichlet series, while
the separate pole correction is retained for the true transform.
-/

open MeasureTheory
open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The two additional constant factors on the displaced zeta contour. -/
def plattZetaRightFactor (m : ℕ) : ℝ :=
  (Real.sqrt Real.pi) ^ (-plattRightShift m) *
    ‖riemannZeta ((2 * (m : ℝ) + 1 : ℝ) : ℂ)‖

theorem plattZetaRightFactor_nonneg (m : ℕ) : 0 ≤ plattZetaRightFactor m := by
  unfold plattZetaRightFactor
  positivity

/-- Pointwise domination by the already integrable Gamma contour norm. -/
theorem norm_plattZetaContourIntegrand_right_le (m k : ℕ) (hm : 1 ≤ m)
    (t₀ h x v : ℝ) :
    ‖plattZetaContourIntegrand k t₀ h x
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)‖ ≤
      plattZetaRightFactor m * ‖plattContourIntegrand k t₀ h x
        ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)‖ := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : (plattZetaArgument t₀
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)).re =
        2 * (m : ℝ) + 1 := by
    simp only [plattZetaArgument_re, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    unfold plattRightShift
    ring
  have hb := norm_riemannZeta_le_norm_real (s := plattZetaArgument t₀
    ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) (by rw [hr]; linarith)
  rw [hr] at hb
  simp only [plattZetaContourIntegrand, norm_mul, norm_plattPiPhase, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add, plattZetaRightFactor]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- The genuine Dirichlet series has the full exponentially decaying contour bound. -/
theorem norm_plattDirichletSeries_le_right (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    ‖plattDirichletSeries k t₀ h x‖ ≤
      plattZetaRightFactor m *
        (Real.exp ((plattRightShift m) ^ 2 / (2 * h ^ 2) -
          2 * Real.pi * x * plattRightShift m) * plattScalarCMajorant m k t₀ h) := by
  rw [← integral_plattZetaContourIntegrand_right_eq_series m k hm ht₀ hh]
  apply (norm_integral_le_integral_norm _).trans
  have hi := integral_mono (integrable_plattZetaContourIntegrand_right m k hm ht₀ hh x).norm
    ((integrable_plattContourIntegrand_right m k hm ht₀ hh x).norm.const_mul
      (plattZetaRightFactor m)) (norm_plattZetaContourIntegrand_right_le m k hm t₀ h x)
  rw [integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left
    (integral_norm_plattContourIntegrand_right_le m k hm ht₀ hh x)
    (plattZetaRightFactor_nonneg m))

/-- The actual Fourier transform includes the complete crossed pole correction. -/
theorem norm_fourier_plattZetaWindow_le_right (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    ‖𝓕 (plattZetaWindow k t₀ h) x‖ ≤
      plattZetaRightFactor m *
        (Real.exp ((plattRightShift m) ^ 2 / (2 * h ^ 2) -
          2 * Real.pi * x * plattRightShift m) * plattScalarCMajorant m k t₀ h) +
        2 * Real.pi * ‖plattZetaContourResidueValue k t₀ h x‖ := by
  rw [fourier_plattZetaWindow_eq_series_sub_residue k ht₀ hh]
  apply (norm_sub_le _ _).trans
  apply add_le_add (norm_plattDirichletSeries_le_right m k hm ht₀ hh x)
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

end

end PrimeFactorUnimodality
