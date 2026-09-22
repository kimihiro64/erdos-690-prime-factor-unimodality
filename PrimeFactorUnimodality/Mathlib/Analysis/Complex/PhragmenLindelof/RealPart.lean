/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Tactic.Linarith

/-! # A lower bound for the real part on a vertical strip

Apply the strip Phragmen--Lindelof principle to `exp(-f)`. A uniform lower
bound on the real part supplies the growth condition, and nonnegative
boundary values then imply nonnegativity throughout the closed strip.
-/

namespace Complex

open Set Filter Asymptotics
open scoped Topology

/-- A real part bounded below on a strip is nonnegative if it is so on both edges. -/
theorem re_nonneg_of_vertical_strip {f : ℂ → ℂ} {a b M : ℝ} (hab : a < b)
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hbound : ∀ z, a < z.re → z.re < b → -M ≤ (f z).re)
    (ha : ∀ z : ℂ, z.re = a → 0 ≤ (f z).re)
    (hb : ∀ z : ℂ, z.re = b → 0 ≤ (f z).re)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : 0 ≤ (f z).re := by
  have he : DiffContOnCl ℂ (fun w => exp (-(f w))) (re ⁻¹' Ioo a b) :=
    differentiable_exp.comp_diffContOnCl hf.neg
  have hnorm : ‖exp (-(f z))‖ ≤ 1 := by
    apply PhragmenLindelof.vertical_strip he ?_ ?_ ?_ hza hzb
    · refine ⟨0, div_pos Real.pi_pos (sub_pos.mpr hab), 0, ?_⟩
      apply isBigO_iff.mpr
      refine ⟨Real.exp M, ?_⟩
      have hmem : ∀ᶠ w in comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b),
          w ∈ re ⁻¹' Ioo a b :=
        (eventually_principal.mpr (fun _ h => h)).filter_mono inf_le_right
      filter_upwards [hmem] with w hw
      simp only [zero_mul, Real.exp_zero, norm_one, mul_one, norm_exp, neg_re]
      exact Real.exp_le_exp.mpr (by linarith [hbound w hw.1 hw.2])
    · intro w hw
      rw [norm_exp, neg_re, Real.exp_le_one_iff]
      linarith [ha w hw]
    · intro w hw
      rw [norm_exp, neg_re, Real.exp_le_one_iff]
      linarith [hb w hw]
  rw [norm_exp, neg_re, Real.exp_le_one_iff] at hnorm
  linarith

/-- A reflected pair of bounded entire functions needs a comparison on only one strip edge. -/
theorem re_reflected_pair_nonneg_of_boundary {F : ℂ → ℂ} {r δ κ M : ℝ}
    (hr : 0 < r) (hδ : 0 ≤ δ) (hF : Differentiable ℂ F)
    (hbound : ∀ z : ℂ, 0 ≤ z.re → ‖F z‖ ≤ M)
    (hboundary : ∀ z : ℂ, z.re = 0 →
      0 ≤ (F z + F ((r : ℂ) - z) -
        (κ : ℂ) * (F (z + δ) + F ((r : ℂ) - z + δ))).re)
    {z : ℂ} (hz₀ : 0 ≤ z.re) (hzr : z.re ≤ r) :
    0 ≤ (F z + F ((r : ℂ) - z) -
      (κ : ℂ) * (F (z + δ) + F ((r : ℂ) - z + δ))).re := by
  let G : ℂ → ℂ := fun w => F w + F ((r : ℂ) - w) -
    (κ : ℂ) * (F (w + δ) + F ((r : ℂ) - w + δ))
  have hG : Differentiable ℂ G := by
    dsimp [G]
    exact (hF.add (hF.comp ((differentiable_const _).sub differentiable_id))).sub
      ((differentiable_const _).mul
        ((hF.comp (differentiable_id.add_const _)).add
          (hF.comp (((differentiable_const _).sub differentiable_id).add_const _))))
  have hsymm (w : ℂ) : G ((r : ℂ) - w) = G w := by
    dsimp [G]
    rw [sub_sub_cancel]
    ring
  apply re_nonneg_of_vertical_strip hr hG.diffContOnCl
    (M := 2 * M + |κ| * (2 * M)) ?_ hboundary ?_ hz₀ hzr
  · intro w hw₀ hwr
    have h₁ := hbound w hw₀.le
    have h₂ := hbound ((r : ℂ) - w) (by simp only [sub_re, ofReal_re]; linarith)
    have h₃ := hbound (w + δ) (by simp only [add_re, ofReal_re]; linarith)
    have h₄ := hbound ((r : ℂ) - w + δ)
      (by simp only [add_re, sub_re, ofReal_re]; linarith)
    have hn : ‖G w‖ ≤ 2 * M + |κ| * (2 * M) := by
      calc
        _ ≤ ‖F w + F ((r : ℂ) - w)‖ +
            ‖(κ : ℂ) * (F (w + δ) + F ((r : ℂ) - w + δ))‖ := norm_sub_le _ _
        _ ≤ (M + M) + |κ| * (M + M) := by
          rw [norm_mul, norm_real, Real.norm_eq_abs]
          exact add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂))
            (mul_le_mul_of_nonneg_left
              ((norm_add_le _ _).trans (add_le_add h₃ h₄)) (abs_nonneg _))
        _ = _ := by ring
    linarith [(neg_le_abs (G w).re).trans (abs_re_le_norm (G w))]
  · intro w hw
    have hh := hboundary ((r : ℂ) - w) (by simp [hw])
    change 0 ≤ (G ((r : ℂ) - w)).re at hh
    rwa [hsymm] at hh

end Complex
