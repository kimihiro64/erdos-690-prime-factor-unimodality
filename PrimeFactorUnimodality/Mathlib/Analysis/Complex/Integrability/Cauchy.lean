/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Integrability of inverse-square norms on vertical lines

Scaling and translation reduce the inverse-square norm to the real Cauchy
kernel. The scaling proof is adapted from
`Robin1984.integrable_inverseSquare_verticalLine` in the Apache-2.0
repository `kimihiro64/Robin1984`, revision
`bfa72aec0c25c8ee29cefe4449d778ff30412bee`, module
`Robin1984.NicolasLandau.WeightedMellin`. This generalization permits an
arbitrary imaginary part and uses only Mathlib, not the sibling's analytic
or theorem-specific imports.
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

end Complex
