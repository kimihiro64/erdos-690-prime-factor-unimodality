/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exponentially damped monomials on their decreasing ray

Substitute an exponential into Mathlib's logarithm-over-power monotonicity
theorem and take a natural power. This gives the exact turning point
without a new differentiation argument and includes order zero.
-/

namespace Real

/-- A damped natural monomial decreases after its exact turning point. -/
theorem pow_mul_exp_neg_le_of_le (n : ℕ) {a x y : ℝ}
    (ha : 0 < a) (hx : (n : ℝ) / a ≤ x) (hxy : x ≤ y) :
    y ^ n * exp (-a * y) ≤ x ^ n * exp (-a * x) := by
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, one_mul]
    exact exp_le_exp.mpr (by nlinarith)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hratio : 0 < a / (n : ℝ) := div_pos ha hnpos
  have hxpos : 0 < x := (div_pos hnpos ha).trans_le hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hcut : exp (a / (n : ℝ))⁻¹ ≤ exp x :=
    exp_le_exp.mpr (by simpa only [inv_div] using hx)
  have h := log_div_self_rpow_antitoneOn hratio hcut
    (hcut.trans (exp_le_exp.mpr hxy)) (exp_le_exp.mpr hxy)
  have hp := pow_le_pow_left₀
    (by rw [log_exp]; positivity : 0 ≤ log (exp y) / exp y ^ (a / (n : ℝ))) h n
  have heq (v : ℝ) : (log (exp v) / exp v ^ (a / (n : ℝ))) ^ n =
      v ^ n * exp (-a * v) := by
    rw [log_exp, ← exp_mul, div_pow, ← exp_nat_mul]
    have he : (n : ℝ) * (v * (a / (n : ℝ))) = a * v := by field_simp
    rw [he, div_eq_mul_inv, ← exp_neg]
    congr 2
    ring
  rw [heq, heq] at hp
  exact hp

/-- Monotonicity on the whole closed ray includes the turning point itself. -/
theorem antitoneOn_pow_mul_exp_neg (n : ℕ) {a : ℝ} (ha : 0 < a) :
    AntitoneOn (fun x : ℝ => x ^ n * exp (-a * x)) (Set.Ici ((n : ℝ) / a)) := by
  intro x hx y _ hxy
  exact pow_mul_exp_neg_le_of_le n ha hx hxy

end Real
