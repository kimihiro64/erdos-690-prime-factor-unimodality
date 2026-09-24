/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Polynomial Gaussians decay faster than every real power

Transport the positive-half-line asymptotic through the absolute value to
obtain a two-sided estimate usable in Poisson summation.
-/

open Filter Asymptotics

namespace Real

/-- A polynomial Gaussian is negligible compared with every real power at both infinities. -/
theorem abs_pow_mul_exp_neg_mul_sq_isLittleO_cocompact (k : ℕ) {b : ℝ}
    (hb : 0 < b) (s : ℝ) :
    (fun x : ℝ => |x| ^ k * exp (-b * x ^ 2)) =o[cocompact ℝ]
      (fun x : ℝ => |x| ^ s) := by
  have ht := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb (k : ℝ)).trans
    (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) s)
  have habs : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop := by
    have hn : Tendsto (fun x : ℝ => ‖x‖) (cocompact ℝ) atTop :=
      tendsto_norm_cocompact_atTop
    simpa only [Real.norm_eq_abs] using hn
  simpa only [Function.comp_def, rpow_natCast, sq_abs] using ht.comp_tendsto habs

end Real
