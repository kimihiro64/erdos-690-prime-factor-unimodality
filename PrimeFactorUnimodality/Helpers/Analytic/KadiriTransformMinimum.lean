import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformBounds
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.SingleCrossing

/-! # Sharp interval lower bounds for the signed transform

The source `(a1*exp(-u)-a0)*kernel(u)` changes sign at `log(a1/a0)`
when the coefficients are positive. The general single-crossing theorem
therefore bounds the full transform below by the smaller endpoint value.
This preserves cancellation and does not assert global monotonicity of `K`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real MeasureTheory

/-- The signed gap is the real exponential transform of its actual source. -/
theorem kadiriTransformGap_eq_finiteExpTransform (θ a₀ a₁ w : ℝ) :
    kadiriTransformGap θ a₀ a₁ w =
      finiteExpTransform (fun u => (a₁ * exp (-u) - a₀) * kadiriKernel θ u)
        (kadiriSupport θ) w := by
  apply intervalIntegral.integral_congr
  intro u _
  ring

/-- The signed transform has an endpoint minimum on every real interval. -/
theorem min_kadiriTransformGap_endpoints_le {θ a₀ a₁ l r w : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (h₀ : 0 < a₀) (h₁ : 0 < a₁) (hw : w ∈ Set.Icc l r) :
    min (kadiriTransformGap θ a₀ a₁ l) (kadiriTransformGap θ a₀ a₁ r) ≤
      kadiriTransformGap θ a₀ a₁ w := by
  let c := log (a₁ / a₀)
  have he : a₁ * exp (-c) = a₀ := by
    rw [exp_neg, exp_log (div_pos h₁ h₀)]
    field_simp
  simp only [kadiriTransformGap_eq_finiteExpTransform]
  apply min_finiteExpTransform_endpoints_le (c := c) (kadiriSupport_pos hθ).le
    ((by fun_prop : Continuous (fun u : ℝ => a₁ * exp (-u) - a₀)).mul
      (continuous_kadiriKernel θ)).continuousOn _ _ hw
  · intro u hu huc
    have h := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg huc)) h₁.le
    rw [he] at h
    exact mul_nonneg (sub_nonneg.mpr h) (kadiriKernel_nonneg hθ hu)
  · intro u hu hcu
    have h := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hcu)) h₁.le
    rw [he] at h
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (kadiriKernel_nonneg hθ hu)

/-- The two-endpoint minimum is always at least as sharp as separating the transforms. -/
theorem kadiri_separate_transform_bound_le_endpoint_minimum {θ a₀ a₁ l r : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hlr : l ≤ r) :
    a₁ * kadiriKernelExpIntegral θ (l - 1) - a₀ * kadiriKernelExpIntegral θ r ≤
      min (kadiriTransformGap θ a₀ a₁ l) (kadiriTransformGap θ a₀ a₁ r) :=
  le_min (kadiriTransformGap_lower_of_mem_Icc hθ h₀ h₁ ⟨le_rfl, hlr⟩)
    (kadiriTransformGap_lower_of_mem_Icc hθ h₀ h₁ ⟨hlr, le_rfl⟩)

end

end PrimeFactorUnimodality
