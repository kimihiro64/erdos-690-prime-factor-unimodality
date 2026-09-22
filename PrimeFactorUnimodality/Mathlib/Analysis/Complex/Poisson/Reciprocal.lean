/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.Stechkin

/-! # Recovering inverse-height squares from reflected reciprocal kernels

On the closed strip `0 ≤ β ≤ 1`, the two real reciprocal kernels dominate
`1/(1+y²)`. Beyond a positive height cutoff this controls `1/y²` with the
explicit factor `1+1/H²`. No restriction to the middle of the strip is
needed, so a reciprocal-mass identity can be used without RH.
-/

namespace Real

noncomputable section

/-- The two nonnegative numerators add to one and their squares are at most one. -/
theorem one_div_one_add_sq_le_stechkinPair_one {β y : ℝ}
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hy : y ≠ 0) :
    1 / (1 + y ^ 2) ≤ stechkinPair 1 β y := by
  have hy₂ : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hk (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
      x / (1 + y ^ 2) ≤ x / (x ^ 2 + y ^ 2) := by
    apply div_le_div_of_nonneg_left hx₀ (by positivity)
    nlinarith [mul_nonneg hx₀ (sub_nonneg.mpr hx₁)]
  have h := add_le_add (hk (1 - β) (by linarith) (by linarith)) (hk β hβ₀ hβ₁)
  convert h using 1
  · ring
  · simp only [stechkinPair, sub_self, zero_add]

/-- Above a height cutoff, the inverse square is controlled by the paired reciprocal mass. -/
theorem inv_sq_le_stechkinPair_one {β y H : ℝ}
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hH : 0 < H) (hy : H ^ 2 ≤ y ^ 2) :
    1 / y ^ 2 ≤ (1 + 1 / H ^ 2) * stechkinPair 1 β y := by
  have hH₂ : 0 < H ^ 2 := sq_pos_of_pos hH
  have hy₂ : 0 < y ^ 2 := hH₂.trans_le hy
  have hy₀ : y ≠ 0 := by intro he; rw [he] at hy₂; norm_num at hy₂
  have hratio : 1 ≤ y ^ 2 / H ^ 2 := (le_div_iff₀ hH₂).mpr (by simpa using hy)
  have hb : 1 / y ^ 2 ≤ (1 + 1 / H ^ 2) / (1 + y ^ 2) := by
    apply (div_le_div_iff₀ hy₂ (by positivity)).mpr
    simp only [div_eq_mul_inv, one_mul] at hratio ⊢
    nlinarith only [hratio]
  calc
    _ ≤ (1 + 1 / H ^ 2) / (1 + y ^ 2) := hb
    _ = (1 + 1 / H ^ 2) * (1 / (1 + y ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (one_div_one_add_sq_le_stechkinPair_one hβ₀ hβ₁ hy₀) (by positivity)

end

end Real
