/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact finite exponential integrals with a linear weight

Closed endpoint expressions for the exponential and its linearly weighted
integral, including zero exponent. The unweighted nonzero case reuses
`integral_exp_mul_complex`; the weighted case follows
from an explicit antiderivative and the fundamental theorem of calculus.
No sign restriction is imposed on the real interval endpoint.
-/

namespace Complex

noncomputable section

open MeasureTheory

/-- The finite exponential integral, with its removable value at zero exponent. -/
def expIntegral (z : ℂ) (d : ℝ) : ℂ :=
  if z = 0 then (d : ℂ) else (exp (z * d) - 1) / z

/-- The finite exponential integral weighted by distance from the right endpoint. -/
def expLinearIntegral (z : ℂ) (d : ℝ) : ℂ :=
  if z = 0 then (d : ℂ) ^ 2 / 2 else (exp (z * d) - 1 - z * d) / z ^ 2

/-- Exact zero-exponent value, including negative interval orientation. -/
@[simp] theorem expIntegral_zero (d : ℝ) : expIntegral 0 d = d := by simp [expIntegral]

/-- Exact zero-exponent value of the linearly weighted integral. -/
@[simp] theorem expLinearIntegral_zero (d : ℝ) :
    expLinearIntegral 0 d = (d : ℂ) ^ 2 / 2 := by simp [expLinearIntegral]

/-- The branch expression is the actual exponential integral for every complex exponent. -/
theorem integral_exp_eq_expIntegral (z : ℂ) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, exp (z * u)) = expIntegral z d := by
  by_cases hz : z = 0
  · simp [hz]
  · simpa [expIntegral, hz] using
      (integral_exp_mul_complex (a := 0) (b := d) hz)

/-- The branch expression is the actual linearly weighted exponential integral. -/
theorem integral_sub_mul_exp_eq_expLinearIntegral (z : ℂ) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, ((d : ℂ) - u) * exp (z * u)) = expLinearIntegral z d := by
  by_cases hz : z = 0
  · subst z
    simp only [zero_mul, exp_zero, mul_one, expLinearIntegral_zero]
    have he : (fun u : ℝ => (d : ℂ) - u) = fun u : ℝ => ((d - u : ℝ) : ℂ) := by
      funext u
      push_cast
      rfl
    rw [he, intervalIntegral.integral_ofReal]
    have hsplit : (∫ u in (0 : ℝ)..d, d - u) =
        (∫ _ in (0 : ℝ)..d, d) - ∫ u in (0 : ℝ)..d, u :=
      intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _)
    rw [hsplit]
    simp only [intervalIntegral.integral_const, integral_id, sub_zero,
      zero_pow (by decide : 2 ≠ 0), smul_eq_mul]
    push_cast
    ring
  · have hd (u : ℝ) : HasDerivAt
        (fun v : ℝ => exp (z * v) * (((d : ℂ) - v) / z + 1 / z ^ 2))
        (((d : ℂ) - u) * exp (z * u)) u := by
      have he := ((hasDerivAt_id (u : ℂ)).const_mul z).cexp
      have hl := (((hasDerivAt_const (u : ℂ) (d : ℂ)).sub
        (hasDerivAt_id (u : ℂ))).div_const z).add_const (1 / z ^ 2)
      convert! (he.mul hl).comp_ofReal using 1
      dsimp
      field_simp
      ring
    have hi : IntervalIntegrable (fun u : ℝ => ((d : ℂ) - u) * exp (z * u)) volume 0 d :=
      (by fun_prop : Continuous (fun u : ℝ => ((d : ℂ) - u) * exp (z * u))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
    simp only [expLinearIntegral, hz, ↓reduceIte, ofReal_zero, mul_zero, exp_zero,
      sub_zero, sub_self, zero_div, zero_add, one_mul]
    field_simp
    ring

end

end Complex
