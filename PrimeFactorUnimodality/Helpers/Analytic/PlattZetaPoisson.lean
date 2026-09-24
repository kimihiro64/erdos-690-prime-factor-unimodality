import Mathlib.Analysis.Fourier.PoissonSummation
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaFourierAliasing
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaTimeAliasing
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.Scaling
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.RapidDecay

set_option autoImplicit false

/-! # Poisson summation for the genuine zeta window

The two-degree Gaussian bound proves time decay; the contour-plus-pole
envelope proves frequency summability. Thus the actual infinite Fourier
series represents the actual time periodization at every positive period.
The explicit time-alias budget bounds its error against the true window.
-/

open Filter Asymptotics
open scoped FourierTransform

namespace PrimeFactorUnimodality

/-- Positive dilation preserves the decay required by Poisson summation. -/
theorem isBigO_plattZetaWindow_scaled (k : ℕ) (t₀ : ℝ) {h B : ℝ}
    (hh : 0 < h) (hB : 0 < B) :
    (fun x : ℝ => plattZetaWindow k t₀ h (B * x)) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  have hb : 0 < B ^ 2 / (2 * h ^ 2) := by positivity
  have h₀ := (Real.abs_pow_mul_exp_neg_mul_sq_isLittleO_cocompact k hb (-2)).isBigO
    |>.const_mul_left (plattZetaTimeCoeff k t₀ false * B ^ k)
  have h₁ := (Real.abs_pow_mul_exp_neg_mul_sq_isLittleO_cocompact (k + 1) hb (-2)).isBigO
    |>.const_mul_left (plattZetaTimeCoeff k t₀ true * B ^ (k + 1))
  apply (isBigO_of_le (cocompact ℝ) ?_).trans (h₁.add h₀)
  intro x
  have hn := norm_plattZetaWindow_le_polynomialGaussian k t₀ h (B * x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    dsimp only [plattZetaTimeCoeff]
    positivity)]
  apply hn.trans_eq
  rw [show -(1 / (2 * h ^ 2)) * (B * x) ^ 2 = -(B ^ 2 / (2 * h ^ 2)) * x ^ 2 by ring]
  simp only [Fintype.sum_bool, plattZetaTimeDegree, abs_mul, abs_of_pos hB, mul_pow]
  ring

/-- The Fourier transform of every positive dilation is summable on the integer grid. -/
theorem summable_fourier_plattZetaWindow_scaled (k : ℕ)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) :
    Summable (fun n : ℤ => 𝓕 (fun x : ℝ => plattZetaWindow k t₀ h (B * x)) n) := by
  have hs := summable_plattZetaFourierPeriodization k ht₀ hh (inv_pos.mpr hB) 0
  simpa only [Real.fourier_comp_mul_left _ hB.ne', abs_of_pos hB, zero_add,
    div_eq_mul_inv] using hs.const_smul (B⁻¹ : ℝ)

/-- The complete genuine time periodization equals its scaled Fourier series. -/
theorem tsum_plattZetaWindow_eq_fourier_series (k : ℕ)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (v : ℝ) :
    (∑' n : ℤ, plattZetaWindow k t₀ h (v + (n : ℝ) * B)) =
      ((B⁻¹ : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 (plattZetaWindow k t₀ h) ((n : ℝ) / B) *
        fourier n ((v / B : ℝ) : UnitAddCircle) := by
  have hc : Continuous (fun x : ℝ => plattZetaWindow k t₀ h (B * x)) :=
    (continuous_plattZetaWindow k t₀ h).comp (by fun_prop)
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc
    (by norm_num : (1 : ℝ) < 2) (isBigO_plattZetaWindow_scaled k t₀ hh hB)
    (summable_fourier_plattZetaWindow_scaled k ht₀ hh hB) (v / B)
  have he (n : ℤ) : B * (v / B + (n : ℝ)) = v + (n : ℝ) * B := by field_simp
  simp only [he, Real.fourier_comp_mul_left _ hB.ne', abs_of_pos hB,
    Complex.real_smul, mul_assoc] at hp
  rw [tsum_mul_left] at hp
  exact hp

/-- The actual Fourier series approximates the true window with the full time-alias budget. -/
theorem norm_plattZetaFourierSeries_sub_window_le (k : ℕ) {t₀ h B v : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    ‖((B⁻¹ : ℝ) : ℂ) * (∑' n : ℤ, 𝓕 (plattZetaWindow k t₀ h) ((n : ℝ) / B) *
        fourier n ((v / B : ℝ) : UnitAddCircle)) - plattZetaWindow k t₀ h v‖ ≤
      plattZetaTimeAliasBound k t₀ h B := by
  have ht := norm_plattZetaTimePeriodization_sub_le k t₀ hh hB hk hv
  rw [plattZetaTimePeriodization, tsum_plattZetaWindow_eq_fourier_series k ht₀ hh hB v] at ht
  exact ht

end PrimeFactorUnimodality
