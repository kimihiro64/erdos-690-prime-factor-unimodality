/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Polynomial factors do not prevent Gaussian decay

The existing real-power asymptotic bound gives the natural-power limit
used to remove the connecting sides of Gaussian-windowed contours.
-/

open Filter
open scoped Topology

namespace Real

/-- Every fixed natural power times a decaying Gaussian tends to zero. -/
theorem tendsto_pow_mul_exp_neg_mul_sq (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ k * exp (-b * x ^ 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    convert tendsto_neg_atTop_atBot.comp
      ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr tendsto_id)
      using 1
    ext x
    simp only [Function.comp_apply, id_eq, neg_mul]
  simpa only [rpow_natCast] using
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb (k : ℝ)).tendsto_zero_of_tendsto ht

end Real
