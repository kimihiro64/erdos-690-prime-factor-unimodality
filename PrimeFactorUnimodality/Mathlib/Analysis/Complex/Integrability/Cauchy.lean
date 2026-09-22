/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Integrability of inverse powers on vertical lines

Scaling and translation reduce the inverse-square norm to the real Cauchy
kernel. The scaling proof is adapted from
`Robin1984.integrable_inverseSquare_verticalLine` in the Apache-2.0
repository `kimihiro64/Robin1984`, revision
`bfa72aec0c25c8ee29cefe4449d778ff30412bee`, module
`Robin1984.NicolasLandau.WeightedMellin`. This generalization permits an
arbitrary imaginary part and uses only Mathlib, not the sibling's analytic
or theorem-specific imports.

The fractional-power result generalizes
`Robin1984.integrable_three_halves_verticalLine` from
`Robin1984.NicolasLandau.WeightedZeroInterchange` at the same revision.
The majorant here works for every positive line and every power above one.
-/

namespace Complex

open MeasureTheory

/-- A vertical line separated from the origin has an integrable inverse-square norm. -/
theorem integrable_inv_sq_norm_vertical {s : ℂ} (hs : s.re ≠ 0) :
    Integrable (fun t : ℝ => 1 / ‖s + (t : ℂ) * I‖ ^ 2) := by
  have hscaled := (integrable_inv_one_add_sq.comp_div hs).comp_add_left s.im
  apply (hscaled.mul_const (s.re ^ 2)⁻¹).congr
  filter_upwards with t
  have hnorm : ‖s + (t : ℂ) * I‖ ^ 2 = s.re ^ 2 + (s.im + t) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp
    ring
  have hpos : 0 < s.re ^ 2 + (s.im + t) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)
  rw [hnorm]
  field_simp [hs, hpos.ne']

/-- Every inverse power greater than one is integrable on a positive vertical line. -/
theorem integrable_inv_rpow_norm_vertical {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    Integrable (fun t : ℝ => ‖(a : ℂ) + (t : ℂ) * I‖⁻¹ ^ r) := by
  have hbase : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-r)) :=
    integrable_one_add_norm (by simpa using hr)
  have hr₀ : 0 ≤ r := by linarith
  refine (hbase.const_mul ((1 + a⁻¹) ^ r)).mono'
    (by fun_prop) (.of_forall fun t => ?_)
  let z : ℂ := (a : ℂ) + (t : ℂ) * I
  have hre : a ≤ ‖z‖ := by simpa [z] using re_le_norm z
  have him : ‖t‖ ≤ ‖z‖ := by simpa [z, Real.norm_eq_abs] using abs_im_le_norm z
  have hn : 0 < ‖z‖ := ha.trans_le hre
  have hw : 0 < 1 + ‖t‖ := by positivity
  have hratio : 1 ≤ ‖z‖ / a := (le_div_iff₀ ha).mpr (by simpa using hre)
  have hinv : ‖z‖⁻¹ ≤ (1 + a⁻¹) * (1 + ‖t‖)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hn hw).mpr
    simp only [one_mul]
    rw [add_mul, one_mul]
    rw [div_eq_mul_inv, mul_comm ‖z‖] at hratio
    linarith
  change ‖‖z‖⁻¹ ^ r‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hn.le) r)]
  calc
    _ ≤ ((1 + a⁻¹) * (1 + ‖t‖)⁻¹) ^ r :=
      Real.rpow_le_rpow (by positivity) hinv (by linarith)
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_neg_eq_inv_rpow]

end Complex
