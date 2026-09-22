/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Cauchy
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Resolvent
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ThreeHalves

/-! # Integrable majorants for regularized Hadamard atoms

A quadratic contour weight times a genus-one atom is bounded by a
three-halves moment of the zero and two integrable vertical kernels.
Only an upper bound on the zero's real part is needed. This generalizes
`Robin1984.norm_paired_hadamard_atom_mul_le` and
`Robin1984.integrable_paired_xi_atom`, from the Apache-2.0 repository
`kimihiro64/Robin1984`, revision `bfa72aec0c25c8ee29cefe4449d778ff30412bee`,
`WeightedZeroInterchange.lean`; it does not assume zeros lie on one line.
-/

namespace Complex

noncomputable section

open MeasureTheory

/-- The regularized atom loses one power in the contour variable and gains a zero moment. -/
theorem norm_mul_hadamardAtom_le {C : ℝ} (hC : 0 ≤ C) {w z ρ : ℂ}
    (hz : z ≠ 0) (hρ : ρ ≠ 0) (hzρ : z - ρ ≠ 0) (hw : ‖w‖ ≤ C / ‖z‖ ^ 2) :
    ‖w * (1 / (z - ρ) + 1 / ρ)‖ ≤ 2 * C * ‖ρ‖⁻¹ ^ (3 / 2 : ℝ) *
      (‖z‖⁻¹ ^ (3 / 2 : ℝ) + ‖z - ρ‖⁻¹ ^ (3 / 2 : ℝ)) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hdn : 0 < ‖z - ρ‖ := norm_pos_iff.mpr hzρ
  have hTriangle : ‖ρ‖ ≤ ‖z‖ + ‖z - ρ‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le z (z - ρ)
  have hatom : 1 / (z - ρ) + 1 / ρ = z / (ρ * (z - ρ)) := by
    field_simp
    ring
  rw [norm_mul, hatom, norm_div, norm_mul]
  calc
    _ ≤ (C / ‖z‖ ^ 2) * (‖z‖ / (‖ρ‖ * ‖z - ρ‖)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = C * (1 / (‖ρ‖ * ‖z‖ * ‖z - ρ‖)) := by field_simp
    _ ≤ C * (2 * ‖ρ‖⁻¹ ^ (3 / 2 : ℝ) *
        (‖z‖⁻¹ ^ (3 / 2 : ℝ) + ‖z - ρ‖⁻¹ ^ (3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (Real.inv_triple_product_le_three_halves hρn hzn hdn hTriangle) hC
    _ = _ := by ring

/-- Moving a zero's real part left can only increase its distance from the contour. -/
theorem norm_vertical_gap_le {c B : ℝ} (hBc : B < c) {ρ : ℂ} (hρ : ρ.re ≤ B) (t : ℝ) :
    ‖((c - B : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * I‖ ≤
      ‖(c : ℂ) + (t : ℂ) * I - ρ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, add_re, sub_re, ofReal_re,
    mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, add_zero,
    add_im, sub_im, mul_im, mul_one, zero_add]
  nlinarith

/-- Uniform fractional majorant over an entire left half-plane of possible zeros. -/
theorem norm_mul_hadamardAtom_vertical_le {c B C : ℝ}
    (hc : 0 < c) (hBc : B < c) (hC : 0 ≤ C) {ρ w : ℂ}
    (hρ₀ : ρ ≠ 0) (hρ : ρ.re ≤ B) (t : ℝ)
    (hw : ‖w‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    ‖w * (1 / ((c : ℂ) + (t : ℂ) * I - ρ) + 1 / ρ)‖ ≤
      2 * C * ‖ρ‖⁻¹ ^ (3 / 2 : ℝ) *
        (‖(c : ℂ) + (t : ℂ) * I‖⁻¹ ^ (3 / 2 : ℝ) +
          ‖((c - B : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * I‖⁻¹ ^ (3 / 2 : ℝ)) := by
  have hz : (c : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_re] at hre
    exact hc.ne' hre
  have hgap : 0 < ‖((c - B : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * I‖ := by
    have hre := re_le_norm (((c - B : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * I)
    simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hre
    exact (sub_pos.mpr hBc).trans_le hre
  have hnorm := norm_vertical_gap_le hBc hρ t
  have hsub : (c : ℂ) + (t : ℂ) * I - ρ ≠ 0 :=
    norm_pos_iff.mp (hgap.trans_le hnorm)
  apply (norm_mul_hadamardAtom_le hC hz hρ₀ hsub hw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  exact Real.rpow_le_rpow (by positivity) (inv_anti₀ hgap hnorm) (by norm_num)

/-- Each regularized atom is integrable against an integrable contour weight. -/
theorem integrable_mul_hadamardAtom_vertical {H : ℝ → ℂ} (hH : Integrable H)
    {c : ℝ} {ρ : ℂ} (hρ : ρ.re < c) :
    Integrable (fun t : ℝ => H t * (1 / ((c : ℂ) + (t : ℂ) * I - ρ) + 1 / ρ)) := by
  apply ((integrable_div_vertical hH hρ).add (hH.div_const ρ)).congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

end

end Complex
