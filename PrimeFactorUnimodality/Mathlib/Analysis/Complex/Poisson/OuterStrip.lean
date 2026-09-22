/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.Stechkin

/-! # Paired Poisson kernels outside a central strip

Inside the critical strip the first kernel can have negative numerator.
Keeping that sign gives a uniform lower bound for the unshifted pair and
an upper bound for the shifted pair. An explicit cutoff inequality then
proves nonnegativity at every sufficiently separated height. Unlike the
classical Stechkin comparison, this result allows `σ ≤ 1`.
-/

namespace Real

noncomputable section

/-- Lower bound allowing a negative first numerator in the reflected pair. -/
theorem stechkinPair_outer_lower_bound {σ₀ σ β y : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσβ : σ ≤ β) (hβ : β ≤ 1) (hy : y ≠ 0) :
    ((2 * σ₀ - 1) * y ^ 2 + σ₀ - 1) / (y ^ 2 * (1 + y ^ 2)) ≤
      stechkinPair σ β y := by
  have hy₂ : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have ha : σ - β ≤ 0 := sub_nonpos.mpr hσβ
  have hb₀ : 0 ≤ σ - 1 + β := by linarith
  have hb₁ : σ - 1 + β ≤ 1 := by linarith
  have hd₁ : 0 < (σ - β) ^ 2 + y ^ 2 := by positivity
  have hd₂ : 0 < (σ - 1 + β) ^ 2 + y ^ 2 := by positivity
  have h₁ : (σ - β) / y ^ 2 ≤ (σ - β) / ((σ - β) ^ 2 + y ^ 2) := by
    apply (div_le_div_iff₀ hy₂ hd₁).mpr
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg (σ - β))]
  have h₂ : (σ - 1 + β) / (1 + y ^ 2) ≤
      (σ - 1 + β) / ((σ - 1 + β) ^ 2 + y ^ 2) := by
    apply div_le_div_of_nonneg_left hb₀ hd₂
    nlinarith [sq_nonneg (σ - 1 + β), mul_nonneg hb₀ (sub_nonneg.mpr hb₁)]
  have hid : (σ - β) / y ^ 2 + (σ - 1 + β) / (1 + y ^ 2) =
      ((2 * σ - 1) * y ^ 2 + σ - β) / (y ^ 2 * (1 + y ^ 2)) := by
    field_simp
    ring
  calc
    _ ≤ ((2 * σ - 1) * y ^ 2 + σ - β) / (y ^ 2 * (1 + y ^ 2)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.mpr hσ) hy₂.le]
    _ = (σ - β) / y ^ 2 + (σ - 1 + β) / (1 + y ^ 2) := hid.symm
    _ ≤ stechkinPair σ β y := add_le_add h₁ h₂

/-- Shifted positive numerators can both be bounded using the imaginary denominator. -/
theorem stechkinPair_outer_shift_upper_bound {σ₀ σ β δ y : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσβ : σ ≤ β) (hβ : β ≤ 1)
    (hδ : 1 - σ₀ ≤ δ) (hy : y ≠ 0) :
    stechkinPair (σ + δ) β y ≤ (1 + 2 * δ) / y ^ 2 := by
  have hy₂ : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hkernel (x : ℝ) (hx : 0 ≤ x) : x / (x ^ 2 + y ^ 2) ≤ x / y ^ 2 :=
    div_le_div_of_nonneg_left hx hy₂ (by nlinarith [sq_nonneg x])
  calc
    _ ≤ (σ + δ - β) / y ^ 2 + (σ + δ - 1 + β) / y ^ 2 := by
      exact add_le_add (hkernel _ (by linarith)) (hkernel _ (by linarith))
    _ = (2 * σ - 1 + 2 * δ) / y ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hy₂.le

/-- A scalar height inequality suffices for the inside-strip four-kernel comparison. -/
theorem stechkinPair_outer_sub_nonneg {σ₀ σ β κ δ y : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσβ : σ ≤ β) (hβ : β ≤ 1)
    (hκ : 0 ≤ κ) (hδ : 1 - σ₀ ≤ δ) (hy : y ≠ 0)
    (hheight : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * y ^ 2) :
    0 ≤ stechkinPair σ β y - κ * stechkinPair (σ + δ) β y := by
  have hy₂ : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hlo := stechkinPair_outer_lower_bound hσ₀ hσ hσβ hβ hy
  have hup := mul_le_mul_of_nonneg_left
    (stechkinPair_outer_shift_upper_bound hσ₀ hσ hσβ hβ hδ hy) hκ
  have hcompare : κ * ((1 + 2 * δ) / y ^ 2) ≤
      ((2 * σ₀ - 1) * y ^ 2 + σ₀ - 1) / (y ^ 2 * (1 + y ^ 2)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hy₂ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right hheight hy₂.le
    nlinarith only [h]
  linarith

/-- Check the height inequality once at a cutoff, then apply it to every larger height. -/
theorem stechkinPair_outer_sub_nonneg_of_cutoff {σ₀ σ β κ δ H y : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσβ : σ ≤ β) (hβ : β ≤ 1)
    (hκ : 0 ≤ κ) (hδ : 1 - σ₀ ≤ δ) (hH : 0 < H) (hy : H ^ 2 ≤ y ^ 2)
    (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
    (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2) :
    0 ≤ stechkinPair σ β y - κ * stechkinPair (σ + δ) β y := by
  apply stechkinPair_outer_sub_nonneg hσ₀ hσ hσβ hβ hκ hδ
    (by intro h; rw [h] at hy; nlinarith [sq_pos_of_pos hH])
  exact hcut.trans (mul_le_mul_of_nonneg_left hy hgap)

end

end Real
