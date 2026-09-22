/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Paired reciprocal squares and their divided tail integral

The two kernels arising from opposite imaginary parts are positive,
continuous, and decreasing to the right of their poles. After translating
the lower endpoint, their quotient by the original height has integral at
most `2/(t H)`. This is the elementary error integral used in the Lehman
zero-tail estimate, separate from the required zero-counting theorem.
-/

namespace Real

noncomputable section

open MeasureTheory Set

/-- The inverse-square kernels at opposite height shifts. -/
def reciprocalSquarePair (t x : ℝ) : ℝ := 1 / (x - t) ^ 2 + 1 / (x + t) ^ 2

/-- Both poles are excluded on the right-hand interval. -/
theorem reciprocalSquarePair_pos {t x : ℝ} (ht : 0 ≤ t) (hx : t < x) :
    0 < reciprocalSquarePair t x := by
  have hm : 0 < x - t := sub_pos.mpr hx
  have hp : 0 < x + t := by linarith
  unfold reciprocalSquarePair
  positivity

/-- The pair is continuous everywhere to the right of the positive pole. -/
theorem continuousOn_reciprocalSquarePair {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (reciprocalSquarePair t) (Ioi t) := by
  apply ContinuousOn.add
  · exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun x hx => pow_ne_zero _ (ne_of_gt (sub_pos.mpr hx)))
  · exact continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
      (fun x hx => pow_ne_zero _ (by have : t < x := hx; linarith))

/-- Each reciprocal square decreases to the right of both poles. -/
theorem antitoneOn_reciprocalSquarePair {t : ℝ} (ht : 0 ≤ t) :
    AntitoneOn (reciprocalSquarePair t) (Ioi t) := by
  intro x hx y hy hxy
  have hxm : 0 < x - t := sub_pos.mpr hx
  have hxp : 0 < x + t := by have : t < x := hx; linarith
  apply add_le_add
  · exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hxm)
      ((sq_le_sq₀ hxm.le (by linarith)).mpr (by linarith))
  · exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hxp)
      ((sq_le_sq₀ hxp.le (by linarith)).mpr (by linarith))

/-- Translating the lower integration endpoint gives the two denominators in the tail formula. -/
theorem reciprocalSquarePair_add (t x : ℝ) :
    reciprocalSquarePair t (x + t) = 1 / x ^ 2 + 1 / (x + 2 * t) ^ 2 := by
  unfold reciprocalSquarePair
  ring

/-- Elementary inverse-square integrability beyond any positive endpoint. -/
theorem integrableOn_inv_sq_Ioi {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioi H) := by
  apply (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hH).congr_fun
    _ measurableSet_Ioi
  intro x _
  norm_num [rpow_neg_ofNat]

/-- The inverse-square tail is exactly the reciprocal of its endpoint. -/
theorem integral_inv_sq_Ioi {H : ℝ} (hH : 0 < H) :
    (∫ x : ℝ in Ioi H, 1 / x ^ 2) = 1 / H := by
  have h := integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hH
  norm_num [rpow_neg_ofNat, rpow_neg_one] at h
  simpa only [one_div] using h

/-- A pointwise integrable majorant for the divided pair after translation. -/
theorem reciprocalSquarePair_div_add_le {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    reciprocalSquarePair t (x + t) / (x + t) ≤ (2 / t) * (1 / x ^ 2) := by
  have hxp : 0 < x + t := by linarith
  have hx₂ : 0 < x ^ 2 := sq_pos_of_pos hx
  have hpair : reciprocalSquarePair t (x + t) ≤ 2 / x ^ 2 := by
    rw [reciprocalSquarePair_add]
    have hb : 1 / (x + 2 * t) ^ 2 ≤ 1 / x ^ 2 :=
      div_le_div_of_nonneg_left zero_le_one hx₂ (by nlinarith)
    simp only [div_eq_mul_inv, one_mul] at hb ⊢
    linarith
  calc
    _ ≤ (2 / x ^ 2) / (x + t) := div_le_div_of_nonneg_right hpair hxp.le
    _ ≤ (2 / x ^ 2) / t := div_le_div_of_nonneg_left (by positivity) ht (by linarith)
    _ = _ := by ring

/-- The divided translated pair is genuinely integrable, not an undefined integral. -/
theorem integrableOn_reciprocalSquarePair_div_add {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    IntegrableOn (fun x => reciprocalSquarePair t (x + t) / (x + t)) (Ioi H) := by
  apply ((integrableOn_inv_sq_Ioi hH).const_mul (2 / t)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold reciprocalSquarePair; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx₀ : 0 < x := hH.trans hx
  have hp := (reciprocalSquarePair_pos ht.le (by linarith : t < x + t)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp (by linarith))]
  exact reciprocalSquarePair_div_add_le ht hx₀

/-- The explicit divided-pair integral bound used in the Lehman error term. -/
theorem integral_reciprocalSquarePair_div_add_le {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    (∫ x in Ioi H, reciprocalSquarePair t (x + t) / (x + t)) ≤ 2 / (t * H) := by
  calc
    _ ≤ ∫ x in Ioi H, (2 / t) * (1 / x ^ 2) := by
      apply integral_mono_ae (integrableOn_reciprocalSquarePair_div_add ht hH)
        ((integrableOn_inv_sq_Ioi hH).const_mul (2 / t))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact reciprocalSquarePair_div_add_le ht (hH.trans hx)
    _ = _ := by rw [integral_const_mul, integral_inv_sq_Ioi hH]; ring

end

end Real
