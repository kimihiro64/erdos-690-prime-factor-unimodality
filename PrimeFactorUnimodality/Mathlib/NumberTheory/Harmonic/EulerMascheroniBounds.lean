/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # A rational upper bound for the Euler--Mascheroni constant

The fiftieth harmonic number and existing logarithm bounds sharpen
the upper sequence estimate. Only rational arithmetic is evaluated.
-/

namespace Real

/-- The Euler--Mascheroni constant is strictly below 0.59. -/
theorem eulerMascheroniConstant_lt_59_div_100 : eulerMascheroniConstant < (59 / 100 : ℝ) := by
  have hh : (harmonic 50 : ℝ) < 9 / 2 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : Real.log 50 = Real.log 2 + 2 * Real.log 5 := by
    rw [show (50 : ℝ) = 2 * 5 ^ 2 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hg := eulerMascheroniConstant_lt_eulerMascheroniSeq' 50
  norm_num only [eulerMascheroniSeq', show (50 : ℕ) ≠ 0 by decide, ite_false,
    Nat.cast_ofNat] at hg
  rw [hl] at hg
  linarith [log_two_gt_d9, log_five_gt_d9]

end Real
