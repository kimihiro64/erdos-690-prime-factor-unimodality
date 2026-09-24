import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowKernel
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.Measurable

set_option autoImplicit false

/-! # The complex Gamma-window Fourier integrand

Its restriction to the real line is the previously defined kernel times
the actual Fourier phase. An exact norm identity on every horizontal line
retains the Gaussian shift cost and frequency decay separately. No contour
deformation is asserted by these algebraic identities.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Complex continuation of the complete windowed Fourier integrand. -/
def plattContourIntegrand (k : ℕ) (t₀ h u : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma ((1 / 4 : ℂ) + ((z + (t₀ : ℂ)) / 2) * Complex.I) *
    Complex.exp ((Real.pi : ℂ) * (z + (t₀ : ℂ)) / 4 -
      z ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) + ((-2 * Real.pi * u : ℝ) : ℂ) * Complex.I * z) *
      (((-2 * Real.pi : ℝ) : ℂ) * Complex.I * z) ^ k

/-- Measurability holds even away from the pole-free lines used for integration. -/
theorem measurable_plattContourIntegrand (k : ℕ) (t₀ h u : ℝ) :
    Measurable (plattContourIntegrand k t₀ h u) := by
  unfold plattContourIntegrand
  fun_prop

/-- The real-line restriction agrees with the genuine Fourier integrand, including its sign. -/
theorem plattContourIntegrand_real (k : ℕ) (t₀ h u v : ℝ) :
    plattContourIntegrand k t₀ h u (v : ℂ) =
      Complex.exp (((-2 * Real.pi * v * u : ℝ) : ℂ) * Complex.I) *
        plattWindowKernel k t₀ h v := by
  have hg : ((v : ℂ) + (t₀ : ℂ)) / 2 = (((v + t₀) / 2 : ℝ) : ℂ) := by push_cast; ring
  have he : (Real.pi : ℂ) * ((v : ℂ) + (t₀ : ℂ)) / 4 -
      (v : ℂ) ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
      ((-2 * Real.pi * u : ℝ) : ℂ) * Complex.I * (v : ℂ) =
        ((Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2) : ℝ) : ℂ) +
          ((-2 * Real.pi * v * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hp : ((-2 * Real.pi : ℝ) : ℂ) * Complex.I * (v : ℂ) =
      ((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
  unfold plattContourIntegrand plattWindowKernel
  rw [hg, he, hp, Complex.exp_add, ← Complex.ofReal_exp]
  ring

/-- Exact norm on a displaced line; the shift cost has not been dropped or rounded. -/
theorem norm_plattContourIntegrand_on_line (k : ℕ) (t₀ h u v w : ℝ) :
    ‖plattContourIntegrand k t₀ h u ((v : ℂ) + (w : ℂ) * Complex.I)‖ =
      (2 * Real.pi) ^ k * Real.exp (w ^ 2 / (2 * h ^ 2) + 2 * Real.pi * u * w) *
        (‖Complex.Gamma (((1 / 4 - w / 2 : ℝ) : ℂ) +
          (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)‖ *
          Real.exp (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) *
          ‖(w : ℂ) - (v : ℂ) * Complex.I‖ ^ k) := by
  have hg : (1 / 4 : ℂ) + (((v : ℂ) + (w : ℂ) * Complex.I + (t₀ : ℂ)) / 2) *
      Complex.I = ((1 / 4 - w / 2 : ℝ) : ℂ) +
        (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> norm_num
    ring
  have he : ((Real.pi : ℂ) * ((v : ℂ) + (w : ℂ) * Complex.I + (t₀ : ℂ)) / 4 -
      ((v : ℂ) + (w : ℂ) * Complex.I) ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
      ((-2 * Real.pi * u : ℝ) : ℂ) * Complex.I *
        ((v : ℂ) + (w : ℂ) * Complex.I)).re =
      (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) +
        (w ^ 2 / (2 * h ^ 2) + 2 * Real.pi * u * w) := by
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.div_ofNat_re,
      Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hp : ((-2 * Real.pi : ℝ) : ℂ) * Complex.I *
      ((v : ℂ) + (w : ℂ) * Complex.I) =
        ((2 * Real.pi : ℝ) : ℂ) * ((w : ℂ) - (v : ℂ) * Complex.I) := by
    apply Complex.ext <;> norm_num
  unfold plattContourIntegrand
  rw [hg, norm_mul, norm_mul, Complex.norm_exp, he, Real.exp_add,
    norm_pow, hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_pow]
  ring

end

end PrimeFactorUnimodality
