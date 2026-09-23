import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformExpressions

/-! # Exact R6 interfaces and branch regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core
open KadiriTransformExpressions

example (ρ : ℕ → ℝ) (θ : ℚ) : Expr.eval ρ (tangent θ) = Real.tan θ := by
  exact PrimeFactorUnimodality.KadiriTransformExpressions.tangent_eval ρ θ

example (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (support θ) = kadiriSupport θ := by
  exact PrimeFactorUnimodality.KadiriTransformExpressions.support_eval ρ θ

example (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (factor θ) = 1 + Real.tan θ ^ 2 := by
  exact PrimeFactorUnimodality.KadiriTransformExpressions.factor_eval ρ θ

example (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (sineCoefficient θ) = kadiriKernelSineCoefficient θ := by
  exact PrimeFactorUnimodality.KadiriTransformExpressions.sineCoefficient_eval ρ θ

example (ρ : ℕ → ℝ) (θ w : ℚ) :
    Expr.eval ρ (integral θ w) = kadiriKernelExpIntegral θ w := by
  exact PrimeFactorUnimodality.KadiriTransformExpressions.integral_eval ρ θ w

example (ρ : ℕ → ℝ) (θ a₀ a₁ w : ℚ) :
    Expr.eval ρ (gap θ a₀ a₁ w) = kadiriTransformGapClosedForm θ a₀ a₁ w := by
  exact PrimeFactorUnimodality.KadiriTransformExpressions.gap_eval ρ θ a₀ a₁ w

example (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (gap θ 1 (1741 / 1000) 1) =
      kadiriTransformGapClosedForm θ 1 (1741 / 1000) 1 := by
  simpa using gap_eval ρ θ 1 (1741 / 1000) 1

example (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (integral θ (-91 / 100)) = kadiriKernelExpIntegral θ (-91 / 100) := by
  simpa using integral_eval ρ θ (-91 / 100)

end

end PrimeFactorUnimodality.Tests
