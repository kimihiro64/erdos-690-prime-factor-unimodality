import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformClosedForm

/-! # Rigorous endpoint bounds for the signed transform gap

The nonnegative kernel has an increasing exponential transform. Bounding
the two transforms separately gives valid interval bounds for their
signed difference, without assuming that the difference itself is monotone.
All endpoint values are the already-proved closed real formulas.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real MeasureTheory

/-- The exact elementary transform is nonnegative for every real exponent. -/
theorem kadiriKernelExpIntegral_nonneg {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (w : ℝ) :
    0 ≤ kadiriKernelExpIntegral θ w := by
  rw [← integral_kadiriKernel_mul_exp hθ]
  apply intervalIntegral.integral_nonneg (kadiriSupport_pos hθ).le
  intro u hu
  exact mul_nonneg (kadiriKernel_nonneg hθ hu) (Real.exp_pos _).le

/-- Positivity of the actual kernel makes its elementary exponential transform increasing. -/
theorem monotone_kadiriKernelExpIntegral {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) :
    Monotone (kadiriKernelExpIntegral θ) := by
  intro x y hxy
  have hi (w : ℝ) : IntervalIntegrable
      (fun u => kadiriKernel θ u * Real.exp (w * u)) volume 0 (kadiriSupport θ) :=
    ((continuous_kadiriKernel θ).mul (by fun_prop)).intervalIntegrable _ _
  rw [← integral_kadiriKernel_mul_exp hθ, ← integral_kadiriKernel_mul_exp hθ]
  apply intervalIntegral.integral_mono_on (kadiriSupport_pos hθ).le (hi x) (hi y)
  intro u hu
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hxy hu.1)) (kadiriKernel_nonneg hθ hu)

/-- Two endpoint evaluations give a uniform lower bound despite the integrand's sign change. -/
theorem kadiriTransformGap_lower_of_mem_Icc {θ a₀ a₁ l r w : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hw : w ∈ Set.Icc l r) :
    a₁ * kadiriKernelExpIntegral θ (l - 1) - a₀ * kadiriKernelExpIntegral θ r ≤
      kadiriTransformGap θ a₀ a₁ w := by
  rw [kadiriTransformGap_eq_closedForm hθ, kadiriTransformGapClosedForm]
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left (monotone_kadiriKernelExpIntegral hθ (sub_le_sub_right hw.1 1)) h₁)
    (mul_le_mul_of_nonneg_left (monotone_kadiriKernelExpIntegral hθ hw.2) h₀)

/-- The same endpoint comparison gives an upper bound with reversed endpoint choices. -/
theorem kadiriTransformGap_upper_of_mem_Icc {θ a₀ a₁ l r w : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hw : w ∈ Set.Icc l r) :
    kadiriTransformGap θ a₀ a₁ w ≤
      a₁ * kadiriKernelExpIntegral θ (r - 1) - a₀ * kadiriKernelExpIntegral θ l := by
  rw [kadiriTransformGap_eq_closedForm hθ, kadiriTransformGapClosedForm]
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left (monotone_kadiriKernelExpIntegral hθ (sub_le_sub_right hw.2 1)) h₁)
    (mul_le_mul_of_nonneg_left (monotone_kadiriKernelExpIntegral hθ hw.1) h₀)

end

end PrimeFactorUnimodality
