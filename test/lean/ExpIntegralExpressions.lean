import PrimeFactorUnimodality.Helpers.Analytic.ExpIntegralExpressions

/-! # Exact R6 interfaces and branch regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core
open ExpIntegralExpressions

example (ρ : ℕ → ℝ) (w : ℚ) (d : Expr) :
    Expr.eval ρ (exponential w d) = Real.expIntegral w (Expr.eval ρ d) := by
  exact PrimeFactorUnimodality.ExpIntegralExpressions.exponential_eval ρ w d

example (ρ : ℕ → ℝ) (w : ℚ) (d : Expr) :
    Expr.eval ρ (linear w d) = Real.expLinearIntegral w (Expr.eval ρ d) := by
  exact PrimeFactorUnimodality.ExpIntegralExpressions.linear_eval ρ w d

example (ρ : ℕ → ℝ) (w : ℚ) (b d : Expr) :
    Expr.eval ρ (cosine w b d) = Real.expCosIntegral w (Expr.eval ρ b) (Expr.eval ρ d) := by
  exact PrimeFactorUnimodality.ExpIntegralExpressions.cosine_eval ρ w b d

example (ρ : ℕ → ℝ) (w : ℚ) (b d : Expr) :
    Expr.eval ρ (sine w b d) = Real.expSinIntegral w (Expr.eval ρ b) (Expr.eval ρ d) := by
  exact PrimeFactorUnimodality.ExpIntegralExpressions.sine_eval ρ w b d

example (ρ : ℕ → ℝ) (w : ℚ) (b d : Expr) :
    Expr.eval ρ (linearCosine w b d) =
      Real.expLinearCosIntegral w (Expr.eval ρ b) (Expr.eval ρ d) := by
  exact PrimeFactorUnimodality.ExpIntegralExpressions.linearCosine_eval ρ w b d

example (d : Expr) : exponential 0 d = d := by simp [exponential]

example (d : Expr) : linear 0 d = .div (.mul d d) (.const 2) := by simp [linear]

example (ρ : ℕ → ℝ) (d : Expr) :
    Expr.eval ρ (exponential (-1) d) = Real.expIntegral (-1) (Expr.eval ρ d) := by
  simpa using exponential_eval ρ (-1) d

example (ρ : ℕ → ℝ) (b d : Expr) :
    Expr.eval ρ (linearCosine 0 b d) = Real.expLinearCosIntegral 0 (Expr.eval ρ b)
      (Expr.eval ρ d) := by simpa using linearCosine_eval ρ 0 b d

end

end PrimeFactorUnimodality.Tests
