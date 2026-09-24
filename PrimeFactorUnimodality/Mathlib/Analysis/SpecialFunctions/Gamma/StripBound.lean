/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! # Uniform Gamma bounds in positive vertical strips

Euler's integral bounds complex Gamma by its real-parameter value.
Convexity then bounds an entire closed positive strip by its two endpoints.
-/

open MeasureTheory Set

namespace Complex

/-- Taking absolute values in Euler's integral removes the imaginary part. -/
theorem norm_Gamma_le_real_Gamma {s : ℂ} (hs : 0 < s.re) :
    ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Endpoint values control Gamma uniformly in the imaginary direction. -/
theorem norm_Gamma_le_max_of_re_mem_Icc {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : s.re ∈ Icc a b) :
    ‖Gamma s‖ ≤ max (Real.Gamma a) (Real.Gamma b) := by
  exact (norm_Gamma_le_real_Gamma (ha.trans_le hs.1)).trans
    (Real.convexOn_Gamma.le_max_of_mem_Icc ha hb hs)

end Complex
