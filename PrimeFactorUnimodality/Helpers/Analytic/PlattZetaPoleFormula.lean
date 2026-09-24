import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaFourier
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaReality

set_option autoImplicit false

/-! # The complete pole correction in elementary form

The pole's Gamma argument is exactly one half, so its Gamma and pi factors
reduce to a positive quarter power. The remaining exponential and polynomial
are explicit, retaining the complex phase at every natural order. This is
an evaluation identity, not a replacement of the correction by its norm.
-/

namespace PrimeFactorUnimodality

private theorem plattZetaPole_gamma_phase (t₀ : ℝ) :
    Complex.Gamma (1 / 2) * plattPiPhase t₀ (plattZetaPole t₀) =
      ((Real.pi ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hz := (plattZetaArgument_eq_one_iff t₀ (plattZetaPole t₀)).mpr rfl
  rw [plattPiPhase_eq_completed_factor, hz, Complex.Gamma_one_half_eq]
  rw [show (Real.pi : ℂ) ^ (1 / 2 : ℂ) *
      (((Real.pi ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (Real.pi : ℂ) ^ (-1 / 2 : ℂ)) =
      (((Real.pi ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
        ((Real.pi : ℂ) ^ (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-1 / 2 : ℂ))) by ring]
  rw [← Complex.cpow_add _ _ hp]
  norm_num

/-- The exact complex pole correction, with no Gamma evaluation left in the formula. -/
theorem plattZetaPoleCorrection_eq_exp (k : ℕ) (t₀ h x : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x =
      ((2 * Real.pi * Real.pi ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x : ℝ) : ℂ) +
          (((-Real.pi / 8 - t₀ / (2 * h ^ 2) + 2 * Real.pi * t₀ * x : ℝ) : ℂ) * Complex.I)) *
        ((-Real.pi : ℝ) + ((2 * Real.pi * t₀ : ℝ) : ℂ) * Complex.I) ^ k := by
  have hg : (1 / 4 : ℂ) + ((plattZetaPole t₀ + (t₀ : ℂ)) / 2) * Complex.I = 1 / 2 := by
    apply Complex.ext <;> norm_num [plattZetaPole, Complex.mul_re, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
  have he : (Real.pi : ℂ) * (plattZetaPole t₀ + (t₀ : ℂ)) / 4 -
      (plattZetaPole t₀) ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
      ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I * plattZetaPole t₀ =
        (((1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x : ℝ) : ℂ) +
          (((-Real.pi / 8 - t₀ / (2 * h ^ 2) + 2 * Real.pi * t₀ * x : ℝ) : ℂ) * Complex.I)) := by
    apply Complex.ext <;>
      simp only [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.div_ofReal_re,
        Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, plattZetaPole_re, plattZetaPole_im] <;> ring
  have hf : ((-2 * Real.pi : ℝ) : ℂ) * Complex.I * plattZetaPole t₀ =
      ((-Real.pi : ℝ) + ((2 * Real.pi * t₀ : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [plattZetaPole, Complex.mul_re, Complex.mul_im]
    ring
  rw [plattZetaContourResidueValue, plattContourIntegrand, hg, he, hf]
  have hi : (2 * (Real.pi : ℂ) * Complex.I) * -Complex.I = 2 * (Real.pi : ℂ) := by
    calc
      _ = -(2 * (Real.pi : ℂ)) * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  calc
    _ = ((2 * (Real.pi : ℂ) * Complex.I) * -Complex.I) *
        (Complex.Gamma (1 / 2) * plattPiPhase t₀ (plattZetaPole t₀)) *
        Complex.exp (((1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x : ℝ) : ℂ) +
          (((-Real.pi / 8 - t₀ / (2 * h ^ 2) + 2 * Real.pi * t₀ * x : ℝ) : ℂ) * Complex.I)) *
        ((-Real.pi : ℝ) + ((2 * Real.pi * t₀ : ℝ) : ℂ) * Complex.I) ^ k := by ring
    _ = _ := by rw [hi, plattZetaPole_gamma_phase]; push_cast; ring

end PrimeFactorUnimodality
