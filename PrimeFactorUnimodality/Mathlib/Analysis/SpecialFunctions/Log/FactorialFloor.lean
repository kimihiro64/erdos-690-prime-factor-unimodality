/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-! # Uniform half-logarithm bounds for a factorial at a real cutoff

The elementary bounds on Mathlib's Stirling sequence give a sandwich for
`log(n!)` whose error is one half of `log n` plus a fixed constant.
Passing to the floor of a real cutoff retains the half-logarithm coefficient.
These estimates sharpen elementary weighted factorial arguments without a
finite range computation.
-/

namespace Real

/-- The logarithm of a positive integer factorial has a uniform half-logarithm sandwich. -/
theorem log_factorial_half_bounds (n : Nat) (hn : 1 <= n) :
    And
      ((n : Real) * log n - n + log n / 2 + 11 / 12 <= log (n.factorial : Real))
      (log (n.factorial : Real) <= (n : Real) * log n - n + log n / 2 + 1) := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : n - 1 + 1 = n := by omega
  have hl := Stirling.log_stirlingSeq_bounded_by_constant (n - 1)
  rw [hsub] at hl
  have hu := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
  change log (Stirling.stirlingSeq (n - 1 + 1)) <= log (Stirling.stirlingSeq 1) at hu
  rw [hsub] at hu
  have heq : log (Stirling.stirlingSeq n) =
      log (n.factorial : Real) - log n / 2 - log 2 / 2 - (n : Real) * log n + n := by
    rw [Stirling.log_stirlingSeq_formula,
      log_mul (by norm_num) hnpos.ne', log_div hnpos.ne' (exp_pos 1).ne', log_exp]
    ring
  have hone : log (Stirling.stirlingSeq 1) = 1 - log 2 / 2 := by
    rw [Stirling.log_stirlingSeq_formula]
    norm_num [log_div]
    ring
  rw [heq] at hl hu
  rw [hone] at hu
  constructor <;> linarith

/-- A tangent bound for the convex function `x * log x - x`. -/
theorem mul_log_sub_self_slope_le (u v : Real) (hu : 0 < u) (hv : 0 < v) :
    (v * log v - v) - (u * log u - u) <= (v - u) * log v := by
  have h := log_le_sub_one_of_pos (div_pos hv hu)
  rw [log_div hv.ne' hu.ne'] at h
  have hs := mul_le_mul_of_nonneg_left h hu.le
  have heq : u * (v / u - 1) = v - u := by
    field_simp
  rw [heq] at hs
  nlinarith only [hs]

/-- The half-logarithm sandwich holds uniformly at every real cutoff at least one. -/
theorem log_factorial_floor_half_bounds (x : Real) (hx : 1 <= x) :
    And
      (x * log x - x - log x / 2 + 1 / 3 <= log ((Nat.floor x).factorial : Real))
      (log ((Nat.floor x).factorial : Real) <= x * log x - x + log x / 2 + 1) := by
  let n : Nat := Nat.floor x
  have hn : 1 <= n := by
    dsimp only [n]
    rwa [Nat.one_le_floor_iff]
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hxpos : 0 < x := by linarith
  have hnx : (n : Real) <= x := Nat.floor_le hxpos.le
  have hxn : x < (n : Real) + 1 := Nat.lt_floor_add_one x
  have hbounds := log_factorial_half_bounds n hn
  have hlog : log n <= log x := log_le_log hnpos hnx
  have hlogn : 0 <= log (n : Real) := log_nonneg (by exact_mod_cast hn)
  have hlogx : 0 <= log x := log_nonneg hx
  have hmono : (n : Real) * log n - n <= x * log x - x := by
    have h := mul_log_sub_self_slope_le x n hxpos hnpos
    have hp := mul_nonneg (sub_nonneg.mpr hnx) hlogn
    nlinarith only [h, hp]
  have hgap : (x * log x - x) - ((n : Real) * log n - n) <= log x := by
    have h := mul_log_sub_self_slope_le n x hnpos hxpos
    have hp := mul_nonneg (show 0 <= 1 - (x - (n : Real)) by linarith) hlogx
    nlinarith only [h, hp]
  have htwo : x <= 2 * (n : Real) := by
    have hnreal : (1 : Real) <= n := by exact_mod_cast hn
    linarith
  have hloggap : log x - log n <= 1 := by
    have h := log_le_log hxpos htwo
    rw [log_mul (by norm_num) hnpos.ne'] at h
    have htwoLog := log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num only at htwoLog
    linarith
  constructor
  case left =>
    change x * log x - x - log x / 2 + 1 / 3 <= log (n.factorial : Real)
    linarith [hbounds.1]
  case right =>
    change log (n.factorial : Real) <= x * log x - x + log x / 2 + 1
    linarith [hbounds.2]

end Real
