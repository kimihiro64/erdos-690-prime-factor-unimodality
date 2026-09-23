import PrimeFactorUnimodality.Helpers.Analytic.ExpIntegralExpressions
import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformClosedForm

/-! # One expression model for all rational smoothing-transform rows

The endpoint formulas are assembled once and interpreted by a single
semantic theorem. Numerical consumers must still check the complete
expression and every denominator domain. No integral is discretized and
no sign of the signed transform is assumed.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

namespace KadiriTransformExpressions

/-- A rational angle's exact tangent expression. -/
def tangent (θ : ℚ) : Expr := .div (.sin (.const θ)) (.cos (.const θ))

/-- The complete support expression at the chosen rational angle. -/
def support (θ : ℚ) : Expr := .div (.const (-2 * θ)) (tangent θ)

/-- The shared factor multiplying the normal-form kernel. -/
def factor (θ : ℚ) : Expr := .add (.const 1) (.mul (tangent θ) (tangent θ))

/-- Both shifted-sine coefficients are retained. -/
def sineCoefficient (θ : ℚ) : Expr :=
  .sub (.div (.mul (.const 2) (.cos (.const θ))) (.sin (.const θ)))
    (.div (.cos (.const (2 * θ))) (.sin (.const (2 * θ))))

/-- Assemble the exact elementary transform at any rational exponent. -/
def integral (θ w : ℚ) : Expr :=
  let b := tangent θ
  let d := support θ
  .mul (factor θ)
    (.add (.add (.add
      (.add (.mul (.div (factor θ) (.const 2))
        (ExpIntegralExpressions.linearCosine w b d)) (ExpIntegralExpressions.linear w d))
      (.mul (.const 2) (ExpIntegralExpressions.exponential w d)))
      (ExpIntegralExpressions.cosine w b d))
      (.mul (sineCoefficient θ) (ExpIntegralExpressions.sine w b d)))

/-- The two full transforms form the signed gap without discarding either term. -/
def gap (θ a₀ a₁ w : ℚ) : Expr :=
  .sub (.mul (.const a₁) (integral θ (w - 1))) (.mul (.const a₀) (integral θ w))

/-- The tangent expression evaluates to the actual trigonometric value. -/
theorem tangent_eval (ρ : ℕ → ℝ) (θ : ℚ) : Expr.eval ρ (tangent θ) = Real.tan θ := by
  simp [tangent, Expr.div, Expr.eval, Real.tan_eq_sin_div_cos, div_eq_mul_inv]

/-- The support expression agrees with the analytical support definition. -/
theorem support_eval (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (support θ) = kadiriSupport θ := by
  simp [support, Expr.div, Expr.eval, tangent_eval, kadiriSupport, div_eq_mul_inv]

/-- The factor expression is the complete normal-form prefactor. -/
theorem factor_eval (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (factor θ) = 1 + Real.tan θ ^ 2 := by
  simp [factor, Expr.eval, tangent_eval, pow_two]

/-- The coefficient expression agrees with the exact shifted-sine expansion. -/
theorem sineCoefficient_eval (ρ : ℕ → ℝ) (θ : ℚ) :
    Expr.eval ρ (sineCoefficient θ) = kadiriKernelSineCoefficient θ := by
  simp [sineCoefficient, Expr.div, Expr.eval, kadiriKernelSineCoefficient, div_eq_mul_inv]

/-- Every exponent, including zero, evaluates to the original elementary transform. -/
theorem integral_eval (ρ : ℕ → ℝ) (θ w : ℚ) :
    Expr.eval ρ (integral θ w) = kadiriKernelExpIntegral θ w := by
  simp only [integral, Expr.eval, Expr.div, ExpIntegralExpressions.linearCosine_eval,
    ExpIntegralExpressions.linear_eval, ExpIntegralExpressions.exponential_eval,
    ExpIntegralExpressions.cosine_eval, ExpIntegralExpressions.sine_eval,
    factor_eval, tangent_eval, support_eval, sineCoefficient_eval]
  norm_num [kadiriKernelExpIntegral, div_eq_mul_inv]

/-- A checked expression bounds exactly the signed transform required by the bootstrap. -/
theorem gap_eval (ρ : ℕ → ℝ) (θ a₀ a₁ w : ℚ) :
    Expr.eval ρ (gap θ a₀ a₁ w) = kadiriTransformGapClosedForm θ a₀ a₁ w := by
  simp [gap, Expr.sub, Expr.eval, integral_eval, kadiriTransformGapClosedForm, sub_eq_add_neg]

end KadiriTransformExpressions

end PrimeFactorUnimodality
