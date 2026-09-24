/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Explicit exponential majorants for polynomial Gaussians

The elementary inequality `1 + t <= exp t`, together with the nonnegative
quadratic remainder, gives a tangent exponential at any positive radius.
Past the polynomial Gaussian's peak its rate is negative, allowing exact
geometric tail estimates without incomplete Gamma evaluations.
-/

namespace Real

/-- The logarithmic tangent majorizes a polynomial Gaussian on the whole positive half-line. -/
theorem pow_mul_exp_neg_mul_sq_le_tangent (k : ℕ) {b R x : ℝ}
    (hb : 0 ≤ b) (hR : 0 < R) (hx : 0 ≤ x) :
    x ^ k * exp (-b * x ^ 2) ≤
      R ^ k * exp (-b * R ^ 2) * exp (((k : ℝ) / R - 2 * b * R) * (x - R)) := by
  have hl : x ≤ R * exp ((x - R) / R) := by
    have he := mul_le_mul_of_nonneg_left (add_one_le_exp ((x - R) / R)) hR.le
    have hi : R * (((x - R) / R) + 1) = x := by field_simp; ring
    rwa [hi] at he
  have hp := pow_le_pow_left₀ hx hl k
  have he : (k : ℝ) * ((x - R) / R) + -b * x ^ 2 ≤
      -b * R ^ 2 + ((k : ℝ) / R - 2 * b * R) * (x - R) := by
    have hs := mul_nonneg hb (sq_nonneg (x - R))
    have hi : (k : ℝ) * ((x - R) / R) = (k : ℝ) / R * (x - R) := by ring
    rw [hi]
    nlinarith
  calc
    _ ≤ (R * exp ((x - R) / R)) ^ k * exp (-b * x ^ 2) :=
      mul_le_mul_of_nonneg_right hp (exp_pos _).le
    _ = R ^ k * exp ((k : ℝ) * ((x - R) / R) + -b * x ^ 2) := by
      rw [mul_pow, ← exp_nat_mul, exp_add]
      ring
    _ ≤ R ^ k * exp (-b * R ^ 2 + ((k : ℝ) / R - 2 * b * R) * (x - R)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (pow_nonneg hR.le _)
    _ = _ := by rw [exp_add]; ring

/-- A two-sided exponential envelope, with its exact coefficient and decay rate. -/
theorem abs_pow_mul_exp_neg_mul_sq_le_exp (k : ℕ) {b R : ℝ}
    (hb : 0 ≤ b) (hR : 0 < R) (x : ℝ) :
    |x| ^ k * exp (-b * x ^ 2) ≤
      (R ^ k * exp (-b * R ^ 2) * exp ((2 * b * R - (k : ℝ) / R) * R)) *
        exp (-(2 * b * R - (k : ℝ) / R) * |x|) := by
  have he : ((k : ℝ) / R - 2 * b * R) * (|x| - R) =
      (2 * b * R - (k : ℝ) / R) * R + -(2 * b * R - (k : ℝ) / R) * |x| := by ring
  have ht := pow_mul_exp_neg_mul_sq_le_tangent k hb hR (abs_nonneg x)
  rw [sq_abs, he, exp_add] at ht
  simpa only [mul_assoc] using ht

end Real
