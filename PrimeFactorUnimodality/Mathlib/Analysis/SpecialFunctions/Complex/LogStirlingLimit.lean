/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogShiftLimit

/-! # The complete complex endpoint normalization in Stirling's formula

The real factorial limit supplies the constant that disappears in a
phase-only argument. The complex shift contributes a term tending to zero,
so both coordinates of the normalization are determined.
-/

open Filter
open scoped Topology

namespace Stirling

/-- The logarithmic factorial normalization tends to the exact Stirling constant. -/
theorem tendsto_log_factorial_normalization :
    Tendsto (fun n : ℕ => Real.log n.factorial + n - ((n : ℝ) + 1 / 2) * Real.log n)
      atTop (𝓝 (Real.log (2 * Real.pi) / 2)) := by
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl := ((Real.continuousAt_log hp).tendsto.comp tendsto_stirlingSeq_sqrt_pi).add_const
    (Real.log 2 / 2)
  have he : Real.log (Real.sqrt Real.pi) + Real.log 2 / 2 = Real.log (2 * Real.pi) / 2 := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    ring
  rw [he] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Function.comp_apply]
  rw [log_stirlingSeq_formula, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn₀,
    Real.log_div hn₀ (Real.exp_ne_zero 1), Real.log_exp]
  ring

end Stirling

namespace Complex

/-- The complete endpoint correction, including the real factorial, has the Stirling limit. -/
theorem tendsto_log_stirling_endpoint (z : ℂ) :
    Tendsto (fun n : ℕ => (Real.log n.factorial : ℂ) + n +
      z * (Real.log n : ℂ) + z - (z + n + 1 / 2) * log (z + n))
      atTop (𝓝 ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)) := by
  have hr := Stirling.tendsto_log_factorial_normalization.ofReal
  have hc := (tendsto_const_nhds (x := z)).sub
    (tendsto_nat_add_mul_log_one_add_div z (z + 1 / 2))
  have hl := hr.add hc
  simp only [sub_self, add_zero] at hl
  have hi : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ofReal_inv, ofReal_natCast, ofReal_zero] using!
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).ofReal
  have h1 : Tendsto (fun n : ℕ => 1 + z / n) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0, h1.eventually_ne (by simp : (1 : ℂ) ≠ 0)]
    with n hn hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : z + n = (n : ℂ) * (1 + z / n) := by field_simp; ring
  have hlog : log (z + n) = (Real.log n : ℂ) + log (1 + z / n) := by
    rw [he]
    simpa only [ofReal_natCast] using log_ofReal_mul hnR hne
  rw [hlog]
  push_cast
  ring

end Complex
