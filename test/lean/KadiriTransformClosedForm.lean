import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapMaster

/-! # Closed-transform and endpoint-bound regressions

Test zero exponent, zero frequency, negative orientation, both normalized
strip endpoints, the actual rescaled transform, and signed-gap bounds.
These examples do not assume a final numerical bootstrap margin.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example (d : ℝ) : Complex.expIntegral 0 d = d := Complex.expIntegral_zero d

example (d : ℝ) : Complex.expLinearIntegral 0 d = (d : ℂ) ^ 2 / 2 :=
  Complex.expLinearIntegral_zero d

example (d : ℝ) : Real.expIntegral 0 d = d := by simp [Real.expIntegral]

example (d : ℝ) : Real.expLinearIntegral 0 d = d ^ 2 / 2 := by simp [Real.expLinearIntegral]

example (z : ℂ) : Complex.expLinearIntegral z 0 = 0 := by
  by_cases hz : z = 0 <;> simp [Complex.expLinearIntegral, hz]

example {b : ℝ} (hb : b ≠ 0) (d : ℝ) :
    Real.expCosIntegral 0 b d = sin (b * d) / b := by
  simp only [Real.expCosIntegral, zero_mul, exp_zero, zero_add, one_mul, sub_zero,
    zero_pow (by decide : 2 ≠ 0)]
  field_simp

example {b : ℝ} (hb : b ≠ 0) (d : ℝ) :
    Real.expLinearCosIntegral 0 b d = (1 - cos (b * d)) / b ^ 2 := by
  simp only [Real.expLinearCosIntegral, zero_mul, exp_zero, zero_add, one_mul, sub_zero,
    zero_sub, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  field_simp
  ring

example {w : ℝ} (hw : w ≠ 0) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, Real.exp (w * u) * cos (0 * u)) = Real.expCosIntegral w 0 d :=
  intervalIntegral.integral_exp_mul_cos (Or.inl hw) d

example {b : ℝ} (hb : b ≠ 0) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, (d - u) * (Real.exp (0 * u) * cos (b * u))) =
      Real.expLinearCosIntegral 0 b d :=
  intervalIntegral.integral_sub_mul_exp_mul_cos (Or.inr hb) d

example : (∫ u in (0 : ℝ)..(-1), (-1 - u) * Real.exp (0 * u)) = 1 / 2 := by
  rw [intervalIntegral.integral_sub_mul_exp_eq_expLinearIntegral]
  norm_num [Real.expLinearIntegral]

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (w : ℝ) :
    (∫ u in (0 : ℝ)..kadiriSupport θ, kadiriKernel θ u * Real.exp (w * u)) =
      kadiriKernelExpIntegral θ w := integral_kadiriKernel_mul_exp hθ w

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (a₀ a₁ : ℝ) :
    kadiriTransformGap θ a₀ a₁ 0 =
      a₁ * kadiriKernelExpIntegral θ (-1) - a₀ * kadiriKernelExpIntegral θ 0 := by
  simpa [kadiriTransformGapClosedForm] using kadiriTransformGap_eq_closedForm hθ a₀ a₁ 0

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (a₀ a₁ : ℝ) :
    kadiriTransformGap θ a₀ a₁ 1 =
      a₁ * kadiriKernelExpIntegral θ 0 - a₀ * kadiriKernelExpIntegral θ 1 := by
  simpa [kadiriTransformGapClosedForm] using kadiriTransformGap_eq_closedForm hθ a₀ a₁ 1

example (θ w : ℝ) : kadiriTransformGapClosedForm θ 0 0 w = 0 := by
  simp [kadiriTransformGapClosedForm]

example {θ η σ β : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hηβ : η = 1 - β) (a₀ a₁ : ℝ) :
    a₁ * (Complex.finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((σ - β : ℝ) : ℂ)).re -
      a₀ * (Complex.finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((σ - 1 : ℝ) : ℂ)).re =
      kadiriTransformGapClosedForm θ a₀ a₁ ((1 - σ) / η) :=
  (kadiriWeight_transform_gap_eq hθ hη hηβ a₀ a₁).trans
    (kadiriTransformGap_eq_closedForm hθ a₀ a₁ _)

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (w : ℝ) :
    0 ≤ kadiriKernelExpIntegral θ w := kadiriKernelExpIntegral_nonneg hθ w

example {θ x y : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hxy : x ≤ y) :
    kadiriKernelExpIntegral θ x ≤ kadiriKernelExpIntegral θ y :=
  monotone_kadiriKernelExpIntegral hθ hxy

example {θ a₀ a₁ l r w : ℝ} (hθ : π / 2 < θ ∧ θ < π)
    (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hw : w ∈ Set.Icc l r) :
    a₁ * kadiriKernelExpIntegral θ (l - 1) - a₀ * kadiriKernelExpIntegral θ r ≤
      kadiriTransformGap θ a₀ a₁ w := kadiriTransformGap_lower_of_mem_Icc hθ h₀ h₁ hw

example {θ a₀ a₁ l r w : ℝ} (hθ : π / 2 < θ ∧ θ < π)
    (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hw : w ∈ Set.Icc l r) :
    kadiriTransformGap θ a₀ a₁ w ≤
      a₁ * kadiriKernelExpIntegral θ (r - 1) - a₀ * kadiriKernelExpIntegral θ l :=
  kadiriTransformGap_upper_of_mem_Icc hθ h₀ h₁ hw

example {θ l r w : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hw : w ∈ Set.Icc l r) :
    -kadiriKernelExpIntegral θ r ≤ kadiriTransformGap θ 1 0 w := by
  simpa using kadiriTransformGap_lower_of_mem_Icc hθ (a₀ := 1) (a₁ := 0)
    (by norm_num) le_rfl hw

end

end PrimeFactorUnimodality.Tests
