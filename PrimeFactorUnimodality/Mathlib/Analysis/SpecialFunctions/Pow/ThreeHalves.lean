/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

/-! # A fractional-power bound for three reciprocal factors

The triangle inequality turns a product of three reciprocals into two
integrable three-halves powers and a summable external factor. Adapted from
`Robin1984.inv_rpow_three_halves_eq` and
`Robin1984.inv_triple_product_le_three_halves` in the Apache-2.0 repository
`kimihiro64/Robin1984`, revision `bfa72aec0c25c8ee29cefe4449d778ff30412bee`,
module `Robin1984.NicolasLandau.WeightedZeroInterchange`. These scalar
lemmas do not use that module's Riemann-hypothesis assumption.
-/

namespace Real

/-- A useful algebraic form of an inverse three-halves power. -/
theorem inv_rpow_three_halves_eq {r : ℝ} (hr : 0 < r) :
    r⁻¹ ^ (3 / 2 : ℝ) = 1 / (r * sqrt r) := by
  rw [← rpow_neg_eq_inv_rpow, rpow_neg hr.le]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    rpow_add hr, rpow_one, ← sqrt_eq_rpow, one_div]

/-- A reciprocal triple product with a triangle constraint admits a fractional majorant. -/
theorem inv_triple_product_le_three_halves {R a b : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hTriangle : R ≤ a + b) :
    1 / (R * a * b) ≤ 2 * R⁻¹ ^ (3 / 2 : ℝ) *
      (a⁻¹ ^ (3 / 2 : ℝ) + b⁻¹ ^ (3 / 2 : ℝ)) := by
  rw [inv_rpow_three_halves_eq hR, inv_rpow_three_halves_eq ha,
    inv_rpow_three_halves_eq hb]
  have hOrdered (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v)
      (hRuv : R ≤ u + v) :
      1 / (R * u * v) ≤ 2 * (1 / (R * sqrt R)) * (1 / (u * sqrt u)) := by
    have hProductSq : (sqrt R * sqrt u) ^ 2 ≤ (2 * v) ^ 2 := by
      rw [mul_pow, sq_sqrt hR.le, sq_sqrt hu.le]
      have hRu := mul_le_mul_of_nonneg_right hRuv hu.le
      have huSq := mul_self_le_mul_self hu.le huv
      have hvu := mul_le_mul_of_nonneg_left huv hv.le
      nlinarith [sq_nonneg v]
    have hProduct : sqrt R * sqrt u ≤ 2 * v := by
      nlinarith [sq_nonneg (sqrt R * sqrt u - 2 * v)]
    have hDen : R * sqrt R * (u * sqrt u) / 2 ≤ R * u * v := by
      nlinarith [mul_le_mul_of_nonneg_left hProduct (by positivity : 0 ≤ R * u)]
    calc
      _ ≤ 1 / (R * sqrt R * (u * sqrt u) / 2) :=
        one_div_le_one_div_of_le (by positivity) hDen
      _ = _ := by field_simp
  rcases le_total a b with hab | hba
  · exact (hOrdered a b ha hb hab hTriangle).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have h := hOrdered b a hb ha hba (by linarith)
    rw [show R * b * a = R * a * b by ring] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity))

end Real
