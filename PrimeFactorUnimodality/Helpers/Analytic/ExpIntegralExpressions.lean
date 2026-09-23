import LeanCert.Core.Expr
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpTrig

/-! # Reified endpoint formulas with the zero-exponent branches retained

One expression builder per elementary integral reuses the exact real
endpoint identities. Rational exponents select their removable zero cases
before interval evaluation, so no division by a zero exponent is attempted.
These builders make no numerical bound or denominator-validity assumption.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

namespace ExpIntegralExpressions

/-- Reify the scalar exponential integral, including exponent zero. -/
def exponential (w : ℚ) (d : Expr) : Expr :=
  if w = 0 then d else .div (.sub (.exp (.mul (.const w) d)) (.const 1)) (.const w)

/-- Reify the linearly weighted scalar exponential integral. -/
def linear (w : ℚ) (d : Expr) : Expr :=
  if w = 0 then .div (.mul d d) (.const 2) else
    .div (.sub (.sub (.exp (.mul (.const w) d)) (.const 1)) (.mul (.const w) d))
      (.const (w ^ 2))

/-- Reify the damped cosine integral. -/
def cosine (w : ℚ) (b d : Expr) : Expr :=
  let phase : Expr := .mul b d
  .div (.sub (.mul (.exp (.mul (.const w) d))
    (.add (.mul (.const w) phase.cos) (.mul b phase.sin))) (.const w))
    (.add (.const (w ^ 2)) (.mul b b))

/-- Reify the damped sine integral. -/
def sine (w : ℚ) (b d : Expr) : Expr :=
  let phase : Expr := .mul b d
  .div (.add (.mul (.exp (.mul (.const w) d))
    (.sub (.mul (.const w) phase.sin) (.mul b phase.cos))) b)
    (.add (.const (w ^ 2)) (.mul b b))

/-- Reify the complete linearly weighted cosine expression. -/
def linearCosine (w : ℚ) (b d : Expr) : Expr :=
  let phase : Expr := .mul b d
  let e : Expr := .exp (.mul (.const w) d)
  let denominator : Expr := .add (.const (w ^ 2)) (.mul b b)
  .div (.add
    (.mul (.sub (.const (w ^ 2)) (.mul b b))
      (.sub (.sub (.mul e phase.cos) (.const 1)) (.mul (.const w) d)))
    (.mul (.mul (.const (2 * w)) b) (.sub (.mul e phase.sin) phase)))
    (.mul denominator denominator)

/-- The exponent-zero branch agrees with the original real integral formula. -/
theorem exponential_eval (ρ : ℕ → ℝ) (w : ℚ) (d : Expr) :
    Expr.eval ρ (exponential w d) = Real.expIntegral w (Expr.eval ρ d) := by
  by_cases hw : w = 0 <;>
    simp [exponential, Real.expIntegral, hw, Expr.div, Expr.eval, div_eq_mul_inv]

/-- The weighted scalar expression retains the exact removable value. -/
theorem linear_eval (ρ : ℕ → ℝ) (w : ℚ) (d : Expr) :
    Expr.eval ρ (linear w d) = Real.expLinearIntegral w (Expr.eval ρ d) := by
  by_cases hw : w = 0 <;>
    simp [linear, Real.expLinearIntegral, hw, Expr.div, Expr.eval, div_eq_mul_inv, pow_two]

/-- Reification preserves the complete damped cosine expression. -/
theorem cosine_eval (ρ : ℕ → ℝ) (w : ℚ) (b d : Expr) :
    Expr.eval ρ (cosine w b d) = Real.expCosIntegral w (Expr.eval ρ b) (Expr.eval ρ d) := by
  simp [cosine, Real.expCosIntegral, Expr.div, Expr.eval, div_eq_mul_inv, pow_two]

/-- Reification preserves the complete damped sine expression. -/
theorem sine_eval (ρ : ℕ → ℝ) (w : ℚ) (b d : Expr) :
    Expr.eval ρ (sine w b d) = Real.expSinIntegral w (Expr.eval ρ b) (Expr.eval ρ d) := by
  simp [sine, Real.expSinIntegral, Expr.div, Expr.eval, div_eq_mul_inv, pow_two]

/-- Reification preserves both terms of the linearly weighted cosine expression. -/
theorem linearCosine_eval (ρ : ℕ → ℝ) (w : ℚ) (b d : Expr) :
    Expr.eval ρ (linearCosine w b d) =
      Real.expLinearCosIntegral w (Expr.eval ρ b) (Expr.eval ρ d) := by
  simp [linearCosine, Real.expLinearCosIntegral, Expr.div, Expr.eval, div_eq_mul_inv, pow_two]

end ExpIntegralExpressions

end PrimeFactorUnimodality
