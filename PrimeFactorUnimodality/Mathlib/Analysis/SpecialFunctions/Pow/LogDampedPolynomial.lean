/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDamped

/-! # Polynomial decay in the inverse-logarithmic damping parameter

Two Taylor monomials turn exponential damping into any natural inverse
power of its parameter, at the cost of one height power. The exponent
and polynomial order are arbitrary; no turning-point premise is needed.
-/

namespace Real

/-- Retaining a Taylor monomial twice gives arbitrary polynomial parameter decay. -/
theorem logDampedPower_le_polynomial (n : ℕ) {a q t : ℝ} (ha : 0 < a) (ht : 1 < t) :
    logDampedPower a q t ≤ ((n.factorial : ℝ) ^ 2 / a ^ n) * logDampedPower 0 (q - 1) t := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hl : 0 < Real.log t := Real.log_pos ht
  have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have he := Real.pow_div_factorial_le_exp _ (div_pos ha hl).le n
  have hp := Real.pow_div_factorial_le_exp _ hl.le n
  rw [Real.exp_log htpos] at hp
  have hlog : Real.log t ^ n ≤ (n.factorial : ℝ) * t := by
    have hp' := (div_le_iff₀ hf).mp hp
    nlinarith only [hp']
  have hinv := one_div_le_one_div_of_le (div_pos (pow_pos (div_pos ha hl) n) hf) he
  have he' : Real.exp (-(a / Real.log t)) ≤
      (n.factorial : ℝ) * Real.log t ^ n / a ^ n := by
    rw [Real.exp_neg]
    rw [one_div] at hinv
    refine hinv.trans_eq ?_
    field_simp
    rw [← mul_pow, div_mul_cancel₀ _ hl.ne']
  have hpoly : Real.exp (-(a / Real.log t)) ≤ (n.factorial : ℝ) ^ 2 * t / a ^ n :=
    he'.trans (by
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hf.le) (pow_pos ha n).le
      convert h using 1
      ring)
  have hleft : logDampedPower a q t = Real.exp (-q * Real.log t) *
      Real.exp (-(a / Real.log t)) := by
    rw [logDampedPower, ← Real.exp_add]
    congr 1
  have hright : logDampedPower 0 (q - 1) t = Real.exp (-q * Real.log t) * t := by
    rw [logDampedPower, zero_div, sub_zero,
      show -(q - 1) * Real.log t = -q * Real.log t + Real.log t by ring,
      Real.exp_add, Real.exp_log htpos]
  rw [hleft, hright]
  exact (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le).trans_eq (by ring)

end Real
