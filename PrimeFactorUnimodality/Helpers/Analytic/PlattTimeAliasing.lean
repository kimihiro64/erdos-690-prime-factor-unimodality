import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowPoisson
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.PolynomialGaussianAliasing

set_option autoImplicit false

/-! # The time-side periodization error of the actual Gamma window

A tangent Gaussian bound and exact geometric summation control the omitted
time translates once `B^2 > 4*k*h^2`. The expression retains the proved
quarter-Gamma constant `5` and contains no unevaluated improper integral.
Poisson summation transports the same error to the actual Fourier series.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The complete time periodization, before finite Fourier approximation. -/
def plattTimePeriodization (k : ℕ) (t₀ h B v : ℝ) : ℂ :=
  ∑' n : ℤ, plattWindowKernel k t₀ h (v + (n : ℝ) * B)

/-- A closed bound for both time aliases throughout the central cell. -/
def plattTimeAliasBound (k : ℕ) (h B : ℝ) : ℝ :=
  10 * (Real.pi * B) ^ k * Real.exp (-B ^ 2 / (8 * h ^ 2)) /
    (1 - Real.exp (2 * (k : ℝ) - B ^ 2 / (2 * h ^ 2)))

private theorem plattTimeAlias_decay (k : ℕ) {h B : ℝ} (hh : 0 < h)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) :
    2 * (k : ℝ) < (1 / (2 * h ^ 2)) * B ^ 2 := by
  rw [show (1 / (2 * h ^ 2)) * B ^ 2 = B ^ 2 / (2 * h ^ 2) by ring]
  apply (lt_div_iff₀ (by positivity : 0 < 2 * h ^ 2)).mpr
  nlinarith

private theorem norm_plattWindowKernel_le_polynomialGaussian (k : ℕ) (t₀ h x : ℝ) :
    ‖plattWindowKernel k t₀ h x‖ ≤
      (5 * (2 * Real.pi) ^ k) * |x| ^ k * Real.exp (-(1 / (2 * h ^ 2)) * x ^ 2) := by
  have he : -x ^ 2 / (2 * h ^ 2) = -(1 / (2 * h ^ 2)) * x ^ 2 := by ring
  simpa only [he, mul_pow, mul_assoc] using norm_plattWindowKernel_le_five k t₀ h x

/-- The complete time periodization is convergent on its central cell. -/
theorem summable_plattTimePeriodization (k : ℕ) (t₀ : ℝ) {h B v : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    Summable (fun n : ℤ => plattWindowKernel k t₀ h (v + (n : ℝ) * B)) :=
  Fourier.summable_lattice_of_polynomialGaussian_bound k (by positivity) (by positivity)
    hB (plattTimeAlias_decay k hh hk) hv (norm_plattWindowKernel_le_polynomialGaussian k t₀ h)

/-- The exact Gaussian and polynomial normalization simplify to the closed time-alias formula. -/
theorem norm_plattTimePeriodization_sub_le (k : ℕ) (t₀ : ℝ) {h B v : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    ‖plattTimePeriodization k t₀ h B v - plattWindowKernel k t₀ h v‖ ≤
      plattTimeAliasBound k h B := by
  have ht := Fourier.norm_periodization_sub_le_of_polynomialGaussian_bound k
    (by positivity) (by positivity) hB (plattTimeAlias_decay k hh hk) hv
    (norm_plattWindowKernel_le_polynomialGaussian k t₀ h)
  have hp : (2 * Real.pi) ^ k * (B / 2) ^ k = (Real.pi * B) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  have hn : 2 * (5 * (2 * Real.pi) ^ k) * (B / 2) ^ k = 10 * (Real.pi * B) ^ k := by
    calc
      _ = 10 * ((2 * Real.pi) ^ k * (B / 2) ^ k) := by ring
      _ = _ := by rw [hp]
  have he : -(1 / (2 * h ^ 2)) * (B / 2) ^ 2 = -B ^ 2 / (8 * h ^ 2) := by ring
  have hd : (1 / (2 * h ^ 2)) * B ^ 2 = B ^ 2 / (2 * h ^ 2) := by ring
  simpa only [plattTimePeriodization, plattTimeAliasBound, hn, he, hd] using ht

/-- The geometric denominator is positive, not a totalized division by zero. -/
theorem plattTimeAlias_denominator_pos (k : ℕ) {h B : ℝ} (hh : 0 < h)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) :
    0 < 1 - Real.exp (2 * (k : ℝ) - B ^ 2 / (2 * h ^ 2)) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hd := plattTimeAlias_decay k hh hk
  rw [show (1 / (2 * h ^ 2)) * B ^ 2 = B ^ 2 / (2 * h ^ 2) by ring] at hd
  linarith

/-- The proved Poisson series approximates the true kernel with the same explicit time error. -/
theorem norm_plattFourierSeries_sub_kernel_le (k : ℕ) {t₀ h B v : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (hv : |v| ≤ B / 2) :
    ‖((B⁻¹ : ℝ) : ℂ) * (∑' n : ℤ, 𝓕 (plattWindowKernel k t₀ h) ((n : ℝ) / B) *
        fourier n ((v / B : ℝ) : UnitAddCircle)) - plattWindowKernel k t₀ h v‖ ≤
      plattTimeAliasBound k h B := by
  have ht := norm_plattTimePeriodization_sub_le k t₀ hh hB hk hv
  rw [plattTimePeriodization, tsum_plattWindowKernel_eq_fourier_series k ht₀ hh hB v] at ht
  exact ht

end

end PrimeFactorUnimodality
