import Mathlib.Analysis.Fourier.FourierTransformDeriv
import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowFourier

set_option autoImplicit false

/-! # The weighted Gamma transforms are genuine derivatives

Every polynomial moment of the window is integrable. Differentiation under
the actual Fourier integral therefore identifies all orders with the kernels
used by the discrete transforms. This supplies the derivative side of the
subsequent Taylor approximation, rather than treating its coefficients as
unrelated transforms.
-/

open MeasureTheory
open scoped ContDiff FourierTransform

namespace PrimeFactorUnimodality

/-- Every real polynomial weight of every window order remains integrable. -/
theorem integrable_pow_smul_plattWindowKernel (n k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (fun v : ℝ => v ^ n • plattWindowKernel k t₀ h v) := by
  have hi := (Real.integrable_abs_pow_mul_exp_neg_mul_sq (n + k)
    (by positivity : 0 < 1 / (2 * h ^ 2))).const_mul (5 * (2 * Real.pi) ^ k)
  apply hi.mono'
    ((continuous_pow n).smul (continuous_plattWindowKernel k t₀ h)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  change ‖v ^ n • plattWindowKernel k t₀ h v‖ ≤
    5 * (2 * Real.pi) ^ k * (|v| ^ (n + k) * Real.exp (-(1 / (2 * h ^ 2)) * v ^ 2))
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  have hb := mul_le_mul_of_nonneg_left (norm_plattWindowKernel_le_five k t₀ h v)
    (pow_nonneg (abs_nonneg v) n)
  have he : -v ^ 2 / (2 * h ^ 2) = -(1 / (2 * h ^ 2)) * v ^ 2 := by ring
  rw [he] at hb
  simpa only [mul_pow, pow_add, mul_assoc, mul_left_comm, mul_comm] using hb

/-- The Fourier differentiation multiplier raises the kernel order exactly. -/
theorem plattWindowKernel_add_order (n k : ℕ) (t₀ h v : ℝ) :
    ((-2 * (Real.pi : ℂ) * Complex.I * v) ^ n) • plattWindowKernel k t₀ h v =
      plattWindowKernel (k + n) t₀ h v := by
  have he : -2 * (Real.pi : ℂ) * Complex.I * v =
      (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [he]
  simp only [plattWindowKernel, smul_eq_mul, pow_add]
  ring

/-- The transform is smooth at every real frequency and every natural kernel order. -/
theorem contDiff_fourier_plattWindowKernel (k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (𝓕 (plattWindowKernel k t₀ h)) := by
  apply Real.contDiff_fourier
  intro n hn
  simpa only [norm_smul, norm_pow, Real.norm_eq_abs] using
    (integrable_pow_smul_plattWindowKernel n k t₀ hh).norm

/-- All iterated derivatives of the actual transform are the corresponding weighted transforms. -/
theorem iteratedDeriv_fourier_plattWindowKernel (n k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    iteratedDeriv n (𝓕 (plattWindowKernel k t₀ h)) =
      𝓕 (plattWindowKernel (k + n) t₀ h) := by
  rw [Real.iteratedDeriv_fourier (N := ⊤)
    (fun r _ => integrable_pow_smul_plattWindowKernel r k t₀ hh) (by simp)]
  congr 1
  funext v
  exact plattWindowKernel_add_order n k t₀ h v

/-- In particular, the transforms used by each FFT column are derivatives of the base transform. -/
theorem iteratedDeriv_fourier_plattWindowKernel_zero (n : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    iteratedDeriv n (𝓕 (plattWindowKernel 0 t₀ h)) = 𝓕 (plattWindowKernel n t₀ h) := by
  simpa only [Nat.zero_add] using iteratedDeriv_fourier_plattWindowKernel n 0 t₀ hh

/-- The established moment bound applies to every genuine derivative, uniformly in frequency. -/
theorem norm_iteratedDeriv_fourier_plattWindowKernel_le (n k : ℕ) (t₀ u : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ‖iteratedDeriv n (𝓕 (plattWindowKernel k t₀ h)) u‖ ≤ plattWindowL1Bound (k + n) h := by
  rw [iteratedDeriv_fourier_plattWindowKernel n k t₀ hh]
  exact norm_fourier_plattWindowKernel_le (k + n) t₀ u hh

end PrimeFactorUnimodality
