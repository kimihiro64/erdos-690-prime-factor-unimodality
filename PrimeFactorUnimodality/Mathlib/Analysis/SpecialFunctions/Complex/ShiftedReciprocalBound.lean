/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ShiftedReciprocal

/-! # Height-sensitive reciprocal-power tails

Split the positive ray at the absolute imaginary part. Before the split,
the imaginary part bounds the denominator; afterwards, the real displacement
does. The integrated bound decays with height at every order greater than one.
-/

open MeasureTheory Set

namespace Complex

/-- Any positive lower bound on the denominator norm bounds a reciprocal power. -/
theorem norm_inv_pow_le_rpow_neg (p : ℕ) {w : ℂ} {H : ℝ} (hH : 0 < H) (hw : H ≤ ‖w‖) :
    ‖w⁻¹ ^ p‖ ≤ H ^ (-(p : ℝ)) := by
  rw [norm_pow, norm_inv, Real.rpow_neg hH.le, Real.rpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hH hw) p

/-- A positive lower radius controls the complete integral of reciprocal powers. -/
theorem integral_norm_inv_pow_add_ofReal_le_of_lower_bound {p : ℕ} (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) {H : ℝ} (hH : 0 < H)
    (hB : ∀ x : ℝ, 0 ≤ x → H ≤ ‖z + (x : ℂ)‖) :
    (∫ x : ℝ in Ioi 0, ‖(z + (x : ℂ))⁻¹ ^ p‖) ≤
      (1 + 1 / ((p : ℝ) - 1)) * H ^ (1 - (p : ℝ)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hi : IntegrableOn (fun x : ℝ => ‖(z + (x : ℂ))⁻¹ ^ p‖) (Ioi 0) :=
    (integrableOn_inv_pow_add_ofReal hp hz).norm
  have ht := hi.mono_set (Ioi_subset_Ioi hH.le)
  have hf : IntervalIntegrable (fun x : ℝ => ‖(z + (x : ℂ))⁻¹ ^ p‖) volume 0 H :=
    (((continuousOn_inv_pow_add_ofReal p hz).norm).mono
      (show Icc 0 H ⊆ Ici 0 from fun _ hx => hx.1)).intervalIntegrable_of_Icc hH.le
  have hfirst : (∫ x : ℝ in 0..H, ‖(z + (x : ℂ))⁻¹ ^ p‖) ≤ H * H ^ (-(p : ℝ)) := by
    calc
      _ ≤ ∫ _ : ℝ in 0..H, H ^ (-(p : ℝ)) := by
        apply intervalIntegral.integral_mono_on hH.le hf intervalIntegrable_const
        intro x hx
        exact norm_inv_pow_le_rpow_neg p hH (hB x hx.1)
      _ = _ := by simp [intervalIntegral.integral_const]
  have hlast : (∫ x : ℝ in Ioi H, ‖(z + (x : ℂ))⁻¹ ^ p‖) ≤
      -H ^ (-(p : ℝ) + 1) / (-(p : ℝ) + 1) := by
    rw [← integral_Ioi_rpow_of_lt (by linarith : -(p : ℝ) < -1) hH]
    apply integral_mono_ae ht (integrableOn_Ioi_rpow_of_lt (by linarith) hH)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply norm_inv_pow_le_rpow_neg p (hH.trans hx)
    have hn := re_le_norm (z + (x : ℂ))
    simp only [add_re, ofReal_re] at hn
    linarith
  calc
    _ = (∫ x : ℝ in 0..H, ‖(z + (x : ℂ))⁻¹ ^ p‖) +
        ∫ x : ℝ in Ioi H, ‖(z + (x : ℂ))⁻¹ ^ p‖ :=
      (intervalIntegral.integral_interval_add_Ioi hi ht).symm
    _ ≤ H * H ^ (-(p : ℝ)) - H ^ (-(p : ℝ) + 1) / (-(p : ℝ) + 1) :=
      (add_le_add hfirst hlast).trans_eq (by ring)
    _ = _ := by
      rw [show 1 - (p : ℝ) = -(p : ℝ) + 1 by ring,
        Real.rpow_add hH, Real.rpow_one]
      have hden : (p : ℝ) - 1 ≠ 0 := by linarith
      have hden' : -(p : ℝ) + 1 ≠ 0 := by linarith
      field_simp
      ring

/-- The full norm integral decays like the imaginary height to the power `1-p`. -/
theorem integral_norm_inv_pow_add_ofReal_le_im {p : ℕ} (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) (him : 0 < |z.im|) :
    (∫ x : ℝ in Ioi 0, ‖(z + (x : ℂ))⁻¹ ^ p‖) ≤
      (1 + 1 / ((p : ℝ) - 1)) * |z.im| ^ (1 - (p : ℝ)) :=
  integral_norm_inv_pow_add_ofReal_le_of_lower_bound hp hz him
    (fun x _ => by simpa using abs_im_le_norm (z + (x : ℂ)))

end Complex
