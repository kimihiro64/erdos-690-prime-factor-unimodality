import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaPoisson
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.SincExponential

set_option autoImplicit false

/-! # Sinc interpolation of the actual zeta window at arbitrary real ordinates

Positive grid rate `A` rescales the already proved contour-plus-pole
envelope. Poisson summation and inversion then control the entire sinc
series without assuming a band limit or exact off-grid values. Finite
truncation and approximate sample errors are separate obligations.
-/

open MeasureTheory
open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- Dilation transfers the genuine two-term envelope to the unit sampling grid. -/
theorem norm_fourier_plattZetaWindow_div_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (x : ℝ) :
    ‖𝓕 (fun v : ℝ => plattZetaWindow k t₀ h (A⁻¹ * v)) x‖ ≤
      ∑ i : Bool, (A * plattZetaEnvelopeCoeff m k t₀ h i) *
        Real.exp (-(plattZetaEnvelopeRate m i * A) * |x|) := by
  rw [Real.fourier_comp_mul_left _ (inv_ne_zero hA.ne'), norm_smul, Real.norm_eq_abs]
  simp only [abs_inv, abs_of_pos hA, inv_inv, div_inv_eq_mul]
  apply (mul_le_mul_of_nonneg_left
    (norm_fourier_plattZetaWindow_le_envelope m k hm ht₀ hh (x * A)) hA.le).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [abs_mul, abs_of_pos hA, ← mul_assoc]
  congr 2
  ring

/-- The closed spectral sampling error, including both the contour and crossed pole. -/
def plattSincError (m k : ℕ) (t₀ h A : ℝ) : ℝ :=
  2 * (∑ i : Bool, (A * plattZetaEnvelopeCoeff m k t₀ h i) *
    (Real.exp (-(plattZetaEnvelopeRate m i * A) / 2) / (plattZetaEnvelopeRate m i * A))) +
  2 * (∑ i : Bool, (A * plattZetaEnvelopeCoeff m k t₀ h i) *
    (Real.exp (-(plattZetaEnvelopeRate m i * A) / 2) /
      (1 - Real.exp (-(plattZetaEnvelopeRate m i * A)))))

/-- The integer samples of the genuine window are absolutely summable at every positive rate. -/
theorem summable_norm_plattZetaWindow_samples (k : ℕ) (t₀ : ℝ)
    {h A : ℝ} (hh : 0 < h) (hA : 0 < A) :
    Summable (fun n : ℤ => ‖plattZetaWindow k t₀ h ((n : ℝ) / A)‖) := by
  simpa only [div_eq_mul_inv, mul_comm] using
    Fourier.summable_norm_int_of_rpow_decay (by norm_num : (1 : ℝ) < 2)
      (isBigO_plattZetaWindow_scaled k t₀ hh (inv_pos.mpr hA))

/-- Sinc interpolation converges absolutely, at off-grid as well as grid ordinates. -/
theorem summable_plattZetaWindow_sinc (k : ℕ) (t₀ v : ℝ)
    {h A : ℝ} (hh : 0 < h) (hA : 0 < A) :
    Summable (fun n : ℤ => plattZetaWindow k t₀ h ((n : ℝ) / A) *
      (Real.sinc (Real.pi * (A * v - n)) : ℂ)) :=
  Fourier.summable_sinc_samples (summable_norm_plattZetaWindow_samples k t₀ hh hA) (A * v)

/-- The complete spectral error bounds interpolation of the actual window, for every real input. -/
theorem norm_plattZetaWindow_sub_sinc_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (v : ℝ) :
    ‖plattZetaWindow k t₀ h v - ∑' n : ℤ,
        plattZetaWindow k t₀ h ((n : ℝ) / A) *
          (Real.sinc (Real.pi * (A * v - n)) : ℂ)‖ ≤ plattSincError m k t₀ h A := by
  have hc : Continuous (fun x => plattZetaWindow k t₀ h (A⁻¹ * x)) :=
    (continuous_plattZetaWindow k t₀ h).comp (by fun_prop)
  have hi := (integrable_plattZetaWindow k t₀ hh).comp_mul_left' (inv_ne_zero hA.ne')
  have he := Fourier.norm_sub_sincSeries_le_of_finite_exp_bound hc hi
    (by norm_num : (1 : ℝ) < 2) (isBigO_plattZetaWindow_scaled k t₀ hh (inv_pos.mpr hA))
    (s := Finset.univ) (c := fun i => A * plattZetaEnvelopeCoeff m k t₀ h i)
    (a := fun i => plattZetaEnvelopeRate m i * A)
    (fun i _ => mul_nonneg hA.le (plattZetaEnvelopeCoeff_nonneg m k hm ht₀ hh i))
    (fun i _ => mul_pos (plattZetaEnvelopeRate_pos m i) hA)
    (norm_fourier_plattZetaWindow_div_le m k hm ht₀ hh hA) (A * v)
  have hv : A⁻¹ * (A * v) = v := by rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
  simpa only [hv, plattSincError, div_eq_mul_inv, mul_comm A⁻¹] using he

end

end PrimeFactorUnimodality
