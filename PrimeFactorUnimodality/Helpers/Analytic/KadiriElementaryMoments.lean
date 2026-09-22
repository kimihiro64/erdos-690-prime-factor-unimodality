import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeMoments

/-! # Elementary bounds for every derivative moment

The proved full-support maximum of the second derivative bounds every
absolute moment by a monomial integral. Mathlib evaluates that integral
exactly. This avoids quadrature of the absolute derivative when the
resulting conservative endpoint budget is sufficient.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The monomial envelope for the absolute derivative moment of any natural degree. -/
def kadiriDerivativeMomentElementary (θ : ℝ) (n : ℕ) : ℝ :=
  (-kadiriKernel₂ θ 0) * kadiriSupport θ ^ (n + 1) / (n + 1)

/-- The sharp pointwise derivative maximum bounds every moment on the complete support. -/
theorem kadiriDerivativeMoment_le_elementary {θ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (n : ℕ) :
    kadiriDerivativeMoment θ n ≤ kadiriDerivativeMomentElementary θ n := by
  calc
    _ ≤ ∫ u in (0 : ℝ)..kadiriSupport θ, u ^ n * (-kadiriKernel₂ θ 0) := by
      apply intervalIntegral.integral_mono_on (kadiriSupport_pos hθ).le
        (((continuous_id.pow n).mul (continuous_kadiriKernel₂ θ).abs).intervalIntegrable _ _)
        (by apply Continuous.intervalIntegrable; fun_prop)
      intro u hu
      exact mul_le_mul_of_nonneg_left (abs_kadiriKernel₂_le_neg_zero hθ hu)
        (pow_nonneg hu.1 n)
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, kadiriDerivativeMomentElementary]
      ring

/-- The elementary moment envelope is nonnegative on the admissible angle range. -/
theorem kadiriDerivativeMomentElementary_nonneg {θ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (n : ℕ) :
    0 ≤ kadiriDerivativeMomentElementary θ n :=
  (kadiriDerivativeMoment_nonneg hθ n).trans (kadiriDerivativeMoment_le_elementary hθ n)

end

end PrimeFactorUnimodality
