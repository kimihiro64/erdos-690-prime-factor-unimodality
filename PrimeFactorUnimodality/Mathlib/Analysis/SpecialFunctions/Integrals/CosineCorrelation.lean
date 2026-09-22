/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Integrating a product of translated cosine bumps

An explicit primitive evaluates the correlation of two translated cosine
functions with a constant subtracted. The endpoints are arbitrary, and
the only restriction is that the frequency is nonzero.
-/

open Real

namespace Real

/-- A primitive for two translated cosine factors with the same constant subtracted. -/
theorem hasDerivAt_cosineCorrelationPrimitive {t : ℝ} (ht : t ≠ 0) (u c v : ℝ) :
    HasDerivAt (fun v : ℝ =>
      (v / 2) * cos (t * u) + sin (2 * t * v + t * u) / (4 * t) -
        c * (sin (t * v) + sin (t * (v + u))) / t + c ^ 2 * v)
      ((cos (t * v) - c) * (cos (t * (v + u)) - c)) v := by
  have h₁ := ((hasDerivAt_id v).div_const 2).mul_const (cos (t * u))
  have h₂ := (((hasDerivAt_id v).const_mul (2 * t)).add_const (t * u)).sin.div_const (4 * t)
  have h₃ := ((((hasDerivAt_id v).const_mul t).sin.add
    (((hasDerivAt_id v).add_const u).const_mul t).sin).const_mul c).div_const t
  have h₄ := (hasDerivAt_id v).const_mul (c ^ 2)
  convert ((h₁.add h₂).sub h₃).add h₄ using 1
  · rfl
  · dsimp
    have hprod := two_mul_cos_mul_cos (t * v) (t * (v + u))
    rw [show t * v - t * (v + u) = -(t * u) by ring, cos_neg,
      show t * v + t * (v + u) = 2 * t * v + t * u by ring] at hprod
    field_simp
    ring_nf at hprod ⊢
    nlinarith [hprod]

end Real

namespace intervalIntegral

/-- Exact finite-interval correlation integral for translated cosine bumps. -/
theorem integral_cos_sub_mul_cos_sub {t : ℝ} (ht : t ≠ 0) (u c a b : ℝ) :
    (∫ v in a..b, (cos (t * v) - c) * (cos (t * (v + u)) - c)) =
      ((b / 2) * cos (t * u) + sin (2 * t * b + t * u) / (4 * t) -
        c * (sin (t * b) + sin (t * (b + u))) / t + c ^ 2 * b) -
      ((a / 2) * cos (t * u) + sin (2 * t * a + t * u) / (4 * t) -
        c * (sin (t * a) + sin (t * (a + u))) / t + c ^ 2 * a) := by
  apply integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_cosineCorrelationPrimitive ht u c v)
  apply Continuous.intervalIntegrable
  fun_prop

end intervalIntegral

namespace Real

/-- A primitive for the correlation of the derivatives of two cosine bumps. -/
theorem hasDerivAt_sineCorrelationPrimitive {t : ℝ} (ht : t ≠ 0) (u v : ℝ) :
    HasDerivAt (fun v : ℝ =>
      (v / 2) * cos (t * u) - sin (2 * t * v + t * u) / (4 * t))
      (sin (t * v) * sin (t * (v + u))) v := by
  have h₁ := ((hasDerivAt_id v).div_const 2).mul_const (cos (t * u))
  have h₂ := (((hasDerivAt_id v).const_mul (2 * t)).add_const (t * u)).sin.div_const (4 * t)
  convert h₁.sub h₂ using 1
  · rfl
  · dsimp
    have hprod := two_mul_sin_mul_sin (t * v) (t * (v + u))
    rw [show t * v - t * (v + u) = -(t * u) by ring, cos_neg,
      show t * v + t * (v + u) = 2 * t * v + t * u by ring] at hprod
    field_simp
    ring_nf at hprod ⊢
    nlinarith [hprod]

end Real

namespace intervalIntegral

/-- Exact finite-interval correlation integral for the sine factors. -/
theorem integral_sin_mul_sin_translate {t : ℝ} (ht : t ≠ 0) (u a b : ℝ) :
    (∫ v in a..b, sin (t * v) * sin (t * (v + u))) =
      ((b / 2) * cos (t * u) - sin (2 * t * b + t * u) / (4 * t)) -
      ((a / 2) * cos (t * u) - sin (2 * t * a + t * u) / (4 * t)) := by
  apply integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_sineCorrelationPrimitive ht u v)
  apply Continuous.intervalIntegrable
  fun_prop

end intervalIntegral
