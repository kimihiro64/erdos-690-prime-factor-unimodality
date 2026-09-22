/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Complex-power decay from a real-part gap

Adapted from `BombieriVinogradov.ComplexAnalysis.
norm_real_cpow_div_le_exp_gap_mul_reciprocal`, Apache-2.0 repository
`kimihiro64/bombieri-vinogradov`, revision
`7a1748306e026825ed6a5555516cc2f28989b2ac`,
`Helpers/ComplexAnalysis/CpowDecayBound.lean` (Lean 4.33.1).
Only the Mathlib-dependent leaf is extracted, into namespace `Complex`.
The bound is valid for any complex exponent, without a zero-location
theorem or a hypothesis about a particular L-function.
-/

namespace Complex

theorem continuousOn_ofReal_cpow_Ici {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ s) (Set.Ici a) := by
  intro t ht
  exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr (ha.trans_le ht))).comp
    continuous_ofReal.continuousAt).continuousWithinAt

theorem norm_real_cpow_div_le_exp_gap_mul_reciprocal
    {y δ : ℝ} (hy : 1 ≤ y) {s : ℂ} (hs : s.re ≤ 1 - δ) :
    ‖(y : ℂ) ^ s / s‖ ≤ (y * Real.exp (-δ * Real.log y)) * ‖(1 : ℂ) / s‖ := by
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hExponent : Real.log y * s.re ≤ Real.log y * (1 - δ) :=
    mul_le_mul_of_nonneg_left hs (Real.log_nonneg hy)
  have hPower : ‖(y : ℂ) ^ s‖ ≤ y * Real.exp (-δ * Real.log y) := by
    rw [norm_cpow_eq_rpow_re_of_pos hyPos, Real.rpow_def_of_pos hyPos]
    calc
      Real.exp (Real.log y * s.re) ≤ Real.exp (Real.log y * (1 - δ)) :=
        Real.exp_le_exp.mpr hExponent
      _ = y * Real.exp (-δ * Real.log y) := by
        have he : Real.log y * (1 - δ) = Real.log y + (-δ * Real.log y) := by ring
        rw [he, Real.exp_add, Real.exp_log hyPos]
  calc
    ‖(y : ℂ) ^ s / s‖ = ‖(y : ℂ) ^ s‖ * ‖(1 : ℂ) / s‖ := by
      rw [div_eq_mul_inv, norm_mul, one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right hPower (by positivity)

end Complex
