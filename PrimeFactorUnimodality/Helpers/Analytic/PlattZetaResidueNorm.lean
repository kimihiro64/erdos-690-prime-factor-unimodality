import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaFourier

set_option autoImplicit false

/-! # Exact size of the zeta pole correction

At the zeta pole the Gamma argument is one half. Its exact value and the
norm of the pi phase give the quarter-power coefficient. Taking the norm
only after the complex contour identity recovers the scalar correction in
Platt's Lemma 3.2, without discarding its phase in an equality of transforms.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

/-- The exact norm of the base-order residue, including its frequency and center dependence. -/
theorem norm_plattZetaContourResidueValue_zero (t₀ h x : ℝ) :
    ‖plattZetaContourResidueValue 0 t₀ h x‖ = Real.pi ^ (1 / 4 : ℝ) *
      Real.exp (1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x) := by
  have hg : (1 / 4 : ℂ) + ((plattZetaPole t₀ + (t₀ : ℂ)) / 2) * Complex.I = 1 / 2 := by
    apply Complex.ext <;> norm_num [plattZetaPole, Complex.mul_re, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
  have he : ((Real.pi : ℂ) * (plattZetaPole t₀ + (t₀ : ℂ)) / 4 -
      (plattZetaPole t₀) ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
      ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I * plattZetaPole t₀).re =
        1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x := by
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.div_ofNat_re,
      Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, plattZetaPole_re, plattZetaPole_im]
    ring
  have hc : Real.pi ^ (1 / 2 : ℝ) * (Real.sqrt Real.pi) ^ (-(1 / 2 : ℝ)) =
      Real.pi ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  rw [plattZetaContourResidueValue, norm_mul, norm_neg, Complex.norm_I, one_mul,
    norm_mul, norm_plattPiPhase, plattZetaPole_im, plattContourIntegrand, pow_zero, mul_one,
    norm_mul, hg, Complex.Gamma_one_half_eq,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.norm_exp, he]
  norm_num only [Complex.div_ofNat_re, Complex.one_re]
  calc
    _ = (Real.pi ^ (1 / 2 : ℝ) * (Real.sqrt Real.pi) ^ (-(1 / 2 : ℝ))) *
        Real.exp (1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x) := by ring
    _ = _ := by rw [hc]

/-- Every polynomial order retains the norm of its frequency factor at the pole. -/
theorem norm_plattZetaContourResidueValue (k : ℕ) (t₀ h x : ℝ) :
    ‖plattZetaContourResidueValue k t₀ h x‖ =
      (Real.pi ^ (1 / 4 : ℝ) *
        Real.exp (1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x)) *
      (2 * Real.pi * ‖plattZetaPole t₀‖) ^ k := by
  have he : plattZetaContourResidueValue k t₀ h x =
      plattZetaContourResidueValue 0 t₀ h x *
      (((-2 * Real.pi : ℝ) : ℂ) * Complex.I * plattZetaPole t₀) ^ k := by
    simp only [plattZetaContourResidueValue, plattContourIntegrand, pow_zero, mul_one]
    ring
  rw [he, norm_mul, norm_plattZetaContourResidueValue_zero, norm_pow]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The complete residue has exactly exponential frequency dependence at every order. -/
theorem norm_plattZetaContourResidueValue_eq_zero_mul_exp (k : ℕ) (t₀ h x : ℝ) :
    ‖plattZetaContourResidueValue k t₀ h x‖ =
      ‖plattZetaContourResidueValue k t₀ h 0‖ * Real.exp (-Real.pi * x) := by
  simp only [norm_plattZetaContourResidueValue, mul_zero, sub_zero]
  rw [show 1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x =
    (1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2)) + (-Real.pi * x) by ring, Real.exp_add]
  ring

/-- The actual Fourier/Dirichlet difference has exactly the scalar norm stated in the paper. -/
theorem norm_fourier_plattZetaWindow_sub_series (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {h : ℝ} (hh : 0 < h) (x : ℝ) :
    ‖𝓕 (plattZetaWindow 0 t₀ h) x - plattDirichletSeries 0 t₀ h x‖ =
      2 * Real.pi ^ (5 / 4 : ℝ) *
        Real.exp (1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x) := by
  rw [fourier_plattZetaWindow_eq_series_sub_residue 0 ht₀ hh x,
    sub_sub_cancel_left, norm_neg, norm_mul, norm_plattZetaContourResidueValue_zero]
  have hp : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hc : Real.pi * Real.pi ^ (1 / 4 : ℝ) = Real.pi ^ (5 / 4 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one Real.pi]
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    norm_num
  rw [hp, ← hc]
  ring

end PrimeFactorUnimodality
