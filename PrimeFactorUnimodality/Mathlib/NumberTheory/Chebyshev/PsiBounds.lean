/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.Chebyshev

/-! # Linear psi bounds from elementary logarithmic estimates

Retain the decaying error in Chebyshev's elementary bound instead of replacing
it by a fixed global constant. A single endpoint estimate controls a full ray.
-/

namespace Chebyshev

open Real

/-- A relative logarithmic estimate sharpens the elementary linear psi bound. -/
theorem psi_le_mul_of_log_div_sqrt_le {x r : ℝ} (hx : 1 ≤ x)
    (hr : log x / sqrt x ≤ r) : ψ x ≤ (log 4 + 2 * r) * x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs := sqrt_pos.mpr hxpos
  have hl := (div_le_iff₀ hs).mp hr
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * sqrt x by positivity)
  have he : 2 * sqrt x * (r * sqrt x) = 2 * r * x := by
    calc
      _ = 2 * r * (sqrt x) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt hxpos.le]
  rw [he] at hm
  exact (psi_le hx).trans (by nlinarith only [hm])

/-- An endpoint logarithm and rational square bound give a linear estimate on a ray. -/
theorem psi_le_mul_of_sqrt_cutoff {a x L r : ℝ} (ha : exp 2 ≤ a) (hax : a ≤ x)
    (hr : 0 < r) (hra : r ^ 2 ≤ a) (hL : 0 ≤ L) (hlog : log a ≤ L) :
    ψ x ≤ (log 4 + 2 * (L / r)) * x := by
  have ha1 : 1 ≤ a := (one_le_exp (by norm_num)).trans ha
  have hs : r ≤ sqrt a := (le_sqrt hr.le (by linarith)).mpr hra
  apply psi_le_mul_of_log_div_sqrt_le (ha1.trans hax)
  exact (log_div_sqrt_antitoneOn ha (ha.trans hax) hax).trans
    ((div_le_div_of_nonneg_right hlog (sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left hL hr hs))

end Chebyshev
