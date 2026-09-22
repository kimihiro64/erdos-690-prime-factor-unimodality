/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Derivative of the logarithmic-power kernel

The function `x / log x ^ (n + 1)` occurs in logarithmic-integral estimates.
-/

namespace Real

/-- Derivative of `x / log x ^ (n + 1)` on the positive logarithmic branch. -/
theorem hasDerivAt_id_div_log_pow_succ {n : ℕ} {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => y / log y ^ (n + 1))
      (1 / log x ^ (n + 1) - (n + 1 : ℝ) / log x ^ (n + 2)) x := by
  have hxpos : 0 < x := by linarith
  have hlogne := (log_pos hx).ne'
  have hd := (hasDerivAt_id x).div
    ((hasDerivAt_log hxpos.ne').pow (n + 1)) (pow_ne_zero _ hlogne)
  convert hd using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply, Nat.add_sub_cancel]
    field_simp [hlogne]
    rw [pow_succ]
    push_cast
    ring

end Real
