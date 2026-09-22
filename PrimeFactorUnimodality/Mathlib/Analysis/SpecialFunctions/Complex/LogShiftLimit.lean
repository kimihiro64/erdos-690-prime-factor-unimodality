/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # The endpoint correction in logarithmic sum asymptotics

The imaginary part of the large endpoint term in the trapezoid expansion
of a shifted logarithm sum tends to zero. This follows from the existing
limit of `n * log (1 + z/n)`, with no restriction on the fixed complex shift.
-/

open Filter
open scoped Topology

namespace Complex

/-- The scaled logarithm with an additional fixed shift has the same limit. -/
theorem tendsto_nat_add_mul_log_one_add_div (z c : ℂ) :
    Tendsto (fun n : ℕ => (n + c) * log (1 + z / n)) atTop (𝓝 z) := by
  have hi : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ofReal_inv, ofReal_natCast, ofReal_zero] using!
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).ofReal
  have hz : Tendsto (fun n : ℕ => z / n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hi
  have h1 : Tendsto (fun n : ℕ => 1 + z / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz
  have hl : Tendsto (fun n : ℕ => log (1 + z / n)) atTop (𝓝 0) := by
    simpa only [log_one] using!
      (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp h1
  have hn : Tendsto (fun n : ℕ => (n : ℂ) * log (1 + z / n)) atTop (𝓝 z) := by
    apply tendsto_nat_mul_log_one_add_of_tendsto
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact mul_div_cancel₀ z (by exact_mod_cast hn)
  simpa only [mul_zero, add_zero, ← add_mul] using hn.add (tendsto_const_nhds.mul hl)

/-- Real logarithmic and factorial normalizations do not affect the endpoint phase limit. -/
theorem tendsto_im_log_shift_correction (z : ℂ) :
    Tendsto (fun n : ℕ =>
      (z * (Real.log n : ℂ) + z - (z + n + 1 / 2) * log (z + n)).im)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ofReal_inv, ofReal_natCast, ofReal_zero] using!
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).ofReal
  have h1 : Tendsto (fun n : ℕ => 1 + z / n) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  have hlim := continuous_im.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := z)).sub
      (tendsto_nat_add_mul_log_one_add_div z (z + 1 / 2)))
  simp only [sub_self, zero_im] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0, h1.eventually_ne (by simp : (1 : ℂ) ≠ 0)]
    with n hn hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : z + n = (n : ℂ) * (1 + z / n) := by field_simp; ring
  have hlog : log (z + n) = (Real.log n : ℂ) + log (1 + z / n) := by
    rw [he]
    simpa only [ofReal_natCast] using log_ofReal_mul hnR hne
  have ha : z * (Real.log n : ℂ) + z -
      (z + n + 1 / 2) * ((Real.log n : ℂ) + log (1 + z / n)) =
      (z - (n + (z + 1 / 2)) * log (1 + z / n)) -
        ((n : ℂ) + 1 / 2) * (Real.log n : ℂ) := by ring
  rw [hlog, ha]
  simp only [Function.comp_apply, sub_im, mul_im, add_im, natCast_im, div_ofNat_im,
    one_im, ofReal_im, zero_div, mul_zero, zero_mul, zero_add, add_zero, sub_zero]

end Complex
