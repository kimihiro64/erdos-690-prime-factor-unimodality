/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.IteratedPrimitive
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAveragePrimitive

/-! # Exact differences and height decay of averaged complex powers

Repeated averaging gains one denominator factor per step. The resulting
bound is explicit for every natural order, and its imaginary-part version
exhibits inverse height to power `n+1` without a hypothesis on zero counts.
-/

open Complex Function Set

namespace intervalIntegral

noncomputable section

/-- The averaged divided power is the normalized forward difference of its primitive. -/
theorem iteratedBoxAverageComplex_cpow_div_eq {h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) (n : ℕ) :
    iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ s / s) x =
      ((h : ℂ) ^ n)⁻¹ * ((fwdDiff h)^[n] (cpowPrimitive s n)) x := by
  have he := iteratedBoxAverageComplex_eq_fwdDiff (a := x) hh (cpowPrimitive s)
    (fun k => continuousOn_cpowPrimitive hx s k)
    (fun k t ht => hasDerivAt_cpowPrimitive_succ hs k (hx.trans_le ht)) n le_rfl
  have hz : cpowPrimitive s 0 = fun t : ℝ => (t : ℂ) ^ s / s := funext (cpowPrimitive_zero s)
  rwa [hz] at he

/-- The exact difference identity with the constant product denominator factored out. -/
theorem iteratedBoxAverageComplex_cpow_div_eq_difference {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) (n : ℕ) :
    iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ s / s) x =
      ((fwdDiff h)^[n] (fun t : ℝ => (t : ℂ) ^ (s + n))) x /
        ((h : ℂ) ^ n * cpowPrimitiveDenom s n) := by
  rw [iteratedBoxAverageComplex_cpow_div_eq hh hx hs]
  have he : cpowPrimitive s n =
      (cpowPrimitiveDenom s n)⁻¹ • (fun t : ℝ => (t : ℂ) ^ (s + n)) := by
    funext t
    simp only [cpowPrimitive, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he, fwdDiff_iter_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_inv]
  ring

/-- The finite-support norm estimate retains the complete primitive denominator. -/
theorem norm_iteratedBoxAverageComplex_cpow_div_le {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0)
    (hβ : 0 ≤ s.re) (n : ℕ) :
    ‖iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ s / s) x‖ ≤
      2 ^ n * (x + n * h) ^ (s.re + n) /
        (h ^ n * ‖cpowPrimitiveDenom s n‖) := by
  rw [iteratedBoxAverageComplex_cpow_div_eq hh hx hs, norm_mul, norm_inv,
    norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hb : ∀ t ∈ Icc x (x + n * h), ‖cpowPrimitive s n t‖ ≤
      (x + n * h) ^ (s.re + n) / ‖cpowPrimitiveDenom s n‖ := by
    intro t ht
    rw [cpowPrimitive, norm_div, norm_cpow_eq_rpow_re_of_pos (hx.trans_le ht.1)]
    simp only [add_re, natCast_re]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (hx.trans_le ht.1).le ht.2
        (add_nonneg hβ (Nat.cast_nonneg _))) (norm_nonneg _)
  have hd := norm_fwdDiff_iter_le hh.le n hb
  calc
    _ ≤ (h ^ n)⁻¹ *
        (2 ^ n * ((x + n * h) ^ (s.re + n) / ‖cpowPrimitiveDenom s n‖)) :=
      mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_nonneg hh.le n))
    _ = _ := by ring

/-- Each averaging step gains another inverse-height factor for a nonreal exponent. -/
theorem norm_iteratedBoxAverageComplex_cpow_div_le_height {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0)
    (hβ : 0 ≤ s.re) (n : ℕ) :
    ‖iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ s / s) x‖ ≤
      2 ^ n * (x + n * h) ^ (s.re + n) / (h ^ n * |s.im| ^ (n + 1)) := by
  refine (norm_iteratedBoxAverageComplex_cpow_div_le hh hx
    (add_natCast_ne_zero_of_im_ne_zero hs) hβ n).trans ?_
  have hU : 0 < x + n * h := add_pos_of_pos_of_nonneg hx
    (mul_nonneg (Nat.cast_nonneg _) hh.le)
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (pow_nonneg (by norm_num) n) (Real.rpow_nonneg hU.le _)
  · exact mul_pos (pow_pos hh n) (pow_pos (abs_pos.mpr hs) (n + 1))
  · exact mul_le_mul_of_nonneg_left (pow_abs_im_le_norm_cpowPrimitiveDenom s n)
      (pow_nonneg hh.le n)

end

end intervalIntegral
