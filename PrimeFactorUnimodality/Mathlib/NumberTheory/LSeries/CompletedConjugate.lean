/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! # Conjugation and reality of the completed Riemann zeta function

The Gamma product transfers conjugation from zeta on the positive half-plane.
The functional equation then makes the completed function real on the critical line.
-/

open Complex
open scoped ComplexConjugate

/-- The completed function is the Gamma product on the positive half-plane. -/
theorem completedRiemannZeta_eq_gamma_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs₀ : s ≠ 0 := by intro he; simp [he] at hs
  rw [riemannZeta_def_of_ne_zero hs₀]
  exact (mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)).symm

/-- Conjugation commutes with completed zeta on the positive half-plane. -/
theorem completedRiemannZeta_conj_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq_gamma_mul (by simpa using hs),
    completedRiemannZeta_eq_gamma_mul hs, riemannZeta_conj]
  have hp : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  have he : (Real.pi : ℂ) ^ (-conj s / 2) = conj ((Real.pi : ℂ) ^ (-s / 2)) := by
    simpa only [map_div₀, map_neg, map_ofNat, conj_ofReal] using
      cpow_conj (Real.pi : ℂ) (-s / 2) hp
  simp only [Gammaℝ, map_mul, map_div₀, map_ofNat, ← Gamma_conj, he]

/-- The completed Riemann zeta function has real values on the critical line. -/
theorem conj_completedRiemannZeta_critical (t : ℝ) :
    conj (completedRiemannZeta (1 / 2 + (t : ℂ) * I)) =
      completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  rw [← completedRiemannZeta_conj_of_re_pos (by norm_num)]
  have he : conj (1 / 2 + (t : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) := by
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
    ring
  rw [he, completedRiemannZeta_one_sub]
