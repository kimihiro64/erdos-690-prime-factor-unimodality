/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A three-kernel rational comparison from two endpoint coefficients

After clearing positive quadratic denominators, the numerator is a
quadratic in the square of the height. Nonnegativity of its constant
and leading coefficients forces its middle coefficient nonnegative
when the third scale is at least the other two.
-/

namespace Real

/-- Two coefficient inequalities suffice uniformly at every real height. -/
theorem threeKernel_nonneg {r d b A B C κ : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hdb : d ≤ b) (hrb : r ≤ b) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hP₂ : 0 ≤ A - κ * (B + C))
    (hP₀ : 0 ≤ A * d ^ 2 * b ^ 2 - κ * r ^ 2 * (B * b ^ 2 + C * d ^ 2)) (y : ℝ) :
    0 ≤ A / (r ^ 2 + y ^ 2) - κ * (B / (d ^ 2 + y ^ 2) + C / (b ^ 2 + y ^ 2)) := by
  have hb : 0 < b := hd.trans_le hdb
  have hb₂ : 0 < b ^ 2 := sq_pos_of_pos hb
  have hbd : 0 ≤ b ^ 2 - d ^ 2 := by nlinarith
  have hbr : 0 ≤ b ^ 2 - r ^ 2 := by nlinarith
  have hP₁ : 0 ≤ A * (d ^ 2 + b ^ 2) - κ * (B * (r ^ 2 + b ^ 2) + C * (r ^ 2 + d ^ 2)) := by
    have heq : A * (d ^ 2 + b ^ 2) - κ * (B * (r ^ 2 + b ^ 2) + C * (r ^ 2 + d ^ 2)) =
        b ^ 2 * (A - κ * (B + C)) +
        (A * d ^ 2 * b ^ 2 - κ * r ^ 2 * (B * b ^ 2 + C * d ^ 2)) / b ^ 2 +
        κ * C * (b ^ 2 - d ^ 2) * (b ^ 2 - r ^ 2) / b ^ 2 := by
      field_simp
      ring
    rw [heq]
    exact add_nonneg (add_nonneg (mul_nonneg hb₂.le hP₂) (div_nonneg hP₀ hb₂.le))
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ hC) hbd) hbr) hb₂.le)
  have hrden : 0 < r ^ 2 + y ^ 2 := by positivity
  have hdden : 0 < d ^ 2 + y ^ 2 := by positivity
  have hbden : 0 < b ^ 2 + y ^ 2 := by positivity
  have heq : A / (r ^ 2 + y ^ 2) - κ * (B / (d ^ 2 + y ^ 2) + C / (b ^ 2 + y ^ 2)) =
      ((A - κ * (B + C)) * y ^ 4 +
        (A * (d ^ 2 + b ^ 2) - κ * (B * (r ^ 2 + b ^ 2) + C * (r ^ 2 + d ^ 2))) * y ^ 2 +
        (A * d ^ 2 * b ^ 2 - κ * r ^ 2 * (B * b ^ 2 + C * d ^ 2))) /
      ((r ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) * (b ^ 2 + y ^ 2)) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg (add_nonneg
    (add_nonneg (mul_nonneg hP₂ (by positivity)) (mul_nonneg hP₁ (sq_nonneg y))) hP₀)
    (by positivity)

end Real
