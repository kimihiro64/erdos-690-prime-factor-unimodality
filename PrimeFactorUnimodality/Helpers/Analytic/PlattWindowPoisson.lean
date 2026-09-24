import Mathlib.Analysis.Fourier.PoissonSummation
import PrimeFactorUnimodality.Helpers.Analytic.PlattFourierAliasing
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.Scaling
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.RapidDecay

set_option autoImplicit false

/-! # Poisson summation for the actual Gaussian-windowed Gamma kernel

Polynomial Gaussian decay supplies the time-side hypothesis, and the proved
contour envelope supplies frequency summability. Real dilation then gives
the periodization identity at every positive period, not just the unit lattice.
-/

open Filter Asymptotics
open scoped FourierTransform

namespace PrimeFactorUnimodality

/-- The scaled kernel decays faster than the inverse-square bound required by Poisson. -/
theorem isBigO_plattWindowKernel_scaled (k : ℕ) (t₀ : ℝ) {h B : ℝ}
    (hh : 0 < h) (hB : 0 < B) :
    (fun x : ℝ => plattWindowKernel k t₀ h (B * x)) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  have hb : 0 < B ^ 2 / (2 * h ^ 2) := by positivity
  have ht := (Real.abs_pow_mul_exp_neg_mul_sq_isLittleO_cocompact k hb (-2)).isBigO
    |>.const_mul_left (5 * (2 * Real.pi * B) ^ k)
  apply (isBigO_of_le (cocompact ℝ) ?_).trans ht
  intro x
  have hn := norm_plattWindowKernel_le_five k t₀ h (B * x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  convert hn using 1
  rw [abs_mul, abs_of_pos hB]
  have he : -(B * x) ^ 2 / (2 * h ^ 2) = -(B ^ 2 / (2 * h ^ 2)) * x ^ 2 := by ring
  rw [he]
  ring

/-- The transform of every positive dilation is summable at integer frequencies. -/
theorem summable_fourier_plattWindowKernel_scaled (k : ℕ)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) :
    Summable (fun n : ℤ => 𝓕 (fun x : ℝ => plattWindowKernel k t₀ h (B * x)) n) := by
  have hs := summable_plattFourierPeriodization 1 k (by omega) ht₀ hh
    (A := B⁻¹) (u := 0) (inv_pos.mpr hB) (by simp only [abs_zero]; positivity)
  simpa only [Real.fourier_comp_mul_left _ hB.ne', abs_of_pos hB, zero_add,
    div_eq_mul_inv] using hs.const_smul (B⁻¹ : ℝ)

/-- The true window periodization equals its Fourier series at any positive period. -/
theorem tsum_plattWindowKernel_eq_fourier_series (k : ℕ)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (v : ℝ) :
    (∑' n : ℤ, plattWindowKernel k t₀ h (v + (n : ℝ) * B)) =
      ((B⁻¹ : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 (plattWindowKernel k t₀ h) ((n : ℝ) / B) *
        fourier n ((v / B : ℝ) : UnitAddCircle) := by
  have hc : Continuous (fun x : ℝ => plattWindowKernel k t₀ h (B * x)) :=
    (continuous_plattWindowKernel k t₀ h).comp (by fun_prop)
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc
    (by norm_num : (1 : ℝ) < 2) (isBigO_plattWindowKernel_scaled k t₀ hh hB)
    (summable_fourier_plattWindowKernel_scaled k ht₀ hh hB) (v / B)
  have he (n : ℤ) : B * (v / B + (n : ℝ)) = v + (n : ℝ) * B := by
    field_simp
  simp only [he, Real.fourier_comp_mul_left _ hB.ne', abs_of_pos hB,
    Complex.real_smul, mul_assoc] at hp
  rw [tsum_mul_left] at hp
  exact hp

end PrimeFactorUnimodality
