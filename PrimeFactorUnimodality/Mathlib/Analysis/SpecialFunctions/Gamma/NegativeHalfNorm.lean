/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! # Comparing Gamma norms on positive and negative half-integer lines

The recurrence gives a uniform factor `8/3` between opposite half-integer
lines. Real part `-3/2` requires this factor at height zero. From real part
`-5/2` onwards the comparison holds with factor one. Every bound retains
arbitrary signed imaginary height.
-/

namespace Complex

/-- Negative half-integer vertical lines avoid every pole of Gamma. -/
theorem continuous_Gamma_neg_nat_sub_half (m : ℕ) :
    Continuous (fun t : ℝ => Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (continuousAt_Gamma _ ?_).comp
    (show ContinuousAt (fun t : ℝ =>
      -(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) t by fun_prop)
  intro n hn
  have hr := congrArg re hn
  norm_num at hr
  have hi : 2 * n = 2 * m + 1 := by
    exact_mod_cast (show (2 : ℝ) * n = 2 * m + 1 by linarith)
  omega

private theorem norm_Gamma_opposite_step {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (t : ℝ)
    (h : ‖Gamma (-(a : ℂ) + (t : ℂ) * I)‖ ≤ C * ‖Gamma ((a : ℂ) + (t : ℂ) * I)‖) :
    (a * (a + 1)) * ‖Gamma (-((a + 1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      C * ‖Gamma (((a + 1 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hnz : -((a + 1 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro he
    have hr := congrArg re he
    norm_num at hr
    linarith
  have hpz : (a : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro he
    have hr := congrArg re he
    norm_num at hr
    linarith
  have hn := congrArg norm (Gamma_add_one (-((a + 1 : ℝ) : ℂ) + (t : ℂ) * I) hnz)
  have hp := congrArg norm (Gamma_add_one ((a : ℂ) + (t : ℂ) * I) hpz)
  have he : -((a + 1 : ℝ) : ℂ) + (t : ℂ) * I + 1 = -(a : ℂ) + (t : ℂ) * I := by
    push_cast
    ring
  have he' : (a : ℂ) + (t : ℂ) * I + 1 = ((a + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast
    ring
  rw [he, norm_mul] at hn
  rw [he', norm_mul] at hp
  have hneg : a + 1 ≤ ‖-((a + 1 : ℝ) : ℂ) + (t : ℂ) * I‖ := by
    have hr := abs_re_le_norm (-((a + 1 : ℝ) : ℂ) + (t : ℂ) * I)
    have hre : (-((a + 1 : ℝ) : ℂ) + (t : ℂ) * I).re = -(a + 1) := by simp
    rw [hre, abs_neg, abs_of_pos (by linarith : 0 < a + 1)] at hr
    exact hr
  have hpos : a ≤ ‖(a : ℂ) + (t : ℂ) * I‖ := by
    simpa using re_le_norm ((a : ℂ) + (t : ℂ) * I)
  have hn' := mul_le_mul_of_nonneg_right hneg
    (norm_nonneg (Gamma (-((a + 1 : ℝ) : ℂ) + (t : ℂ) * I)))
  rw [← hn] at hn'
  have hp' := mul_le_mul_of_nonneg_right hpos (norm_nonneg (Gamma ((a : ℂ) + (t : ℂ) * I)))
  rw [← hp] at hp'
  calc
    _ = a * ((a + 1) * ‖Gamma (-((a + 1 : ℝ) : ℂ) + (t : ℂ) * I)‖) := by ring
    _ ≤ a * ‖Gamma (-(a : ℂ) + (t : ℂ) * I)‖ := mul_le_mul_of_nonneg_left hn' ha.le
    _ ≤ a * (C * ‖Gamma ((a : ℂ) + (t : ℂ) * I)‖) := mul_le_mul_of_nonneg_left h ha.le
    _ = C * (a * ‖Gamma ((a : ℂ) + (t : ℂ) * I)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp' hC

private theorem norm_Gamma_neg_half_le (t : ℝ) :
    ‖Gamma (-((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      2 * ‖Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hnz : -((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro he
    have hr := congrArg re he
    norm_num at hr
  have hh := congrArg norm (Gamma_add_one (-((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) hnz)
  have he : -((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + 1 =
      ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
  rw [he, norm_mul] at hh
  have hn : (1 / 2 : ℝ) ≤ ‖-((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ := by
    simpa using abs_re_le_norm (-((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have h := mul_le_mul_of_nonneg_right hn
    (norm_nonneg (Gamma (-((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)))
  rw [← hh] at h
  linarith

private theorem norm_Gamma_neg_three_halves_le (t : ℝ) :
    ‖Gamma (-((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      (8 / 3) * ‖Gamma (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hs := norm_Gamma_opposite_step (a := 1 / 2) (C := 2)
    (by norm_num) (by norm_num) t (norm_Gamma_neg_half_le t)
  norm_num at hs
  push_cast
  linarith

private theorem norm_Gamma_opposite_induction {C : ℝ} (hC : 0 ≤ C) (t : ℝ)
    {n : ℕ} (hn : 1 ≤ n)
    (hbase : ‖Gamma (-(((n : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      C * ‖Gamma ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (m : ℕ) (hm : n ≤ m) :
    ‖Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      C * ‖Gamma ((((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hn.trans hm
    have hs := norm_Gamma_opposite_step (a := (m : ℝ) + 1 / 2)
      (by positivity) hC t ih
    have he : (m : ℝ) + 1 / 2 + 1 = ((m + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
    rw [he] at hs
    have hfactor : (1 : ℝ) ≤ ((m : ℝ) + 1 / 2) * ((m : ℝ) + 1 / 2 + 1) := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hfactor
      (norm_nonneg (Gamma (-((((m + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)))
    rw [he] at hmul
    simp only [one_mul] at hmul
    exact hmul.trans hs

/-- The factor `8/3` works on every pair of opposite half-integer lines. -/
theorem norm_Gamma_neg_nat_sub_half_le (m : ℕ) (t : ℝ) :
    ‖Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      (8 / 3) * ‖Gamma ((((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  by_cases hm : m = 0
  · subst m
    simpa only [Nat.cast_zero, zero_add] using
      (norm_Gamma_neg_half_le t).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 8 / 3) (norm_nonneg _))
  · apply norm_Gamma_opposite_induction (by norm_num) t (n := 1) (by omega) ?_ m (by omega)
    simpa only [Nat.cast_one, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] using
      norm_Gamma_neg_three_halves_le t

/-- Starting at real part `5/2`, the negative-line norm is no larger than the positive-line norm. -/
theorem norm_Gamma_neg_nat_sub_half_le_pos (m : ℕ) (hm : 2 ≤ m) (t : ℝ) :
    ‖Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      ‖Gamma ((((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hbase := norm_Gamma_opposite_step (a := 3 / 2) (C := 8 / 3)
    (by norm_num) (by norm_num) t (norm_Gamma_neg_three_halves_le t)
  norm_num at hbase
  have hb : ‖Gamma (-((5 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      1 * ‖Gamma (((5 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    push_cast
    nlinarith [norm_nonneg (Gamma (-(5 / 2 : ℂ) + (t : ℂ) * I))]
  simpa only [one_mul] using
    norm_Gamma_opposite_induction (by norm_num : (0 : ℝ) ≤ 1) t (n := 2) (by omega)
      (by simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] using hb) m hm

end Complex

namespace Real

/-- The lowest shifted pair shows that the uniform factor `8/3` cannot be reduced. -/
theorem Gamma_neg_three_halves_eq : Gamma (-(3 / 2)) = (8 / 3) * Gamma (3 / 2) := by
  have h₀ := Gamma_add_one (s := -(3 / 2)) (by norm_num)
  have h₁ := Gamma_add_one (s := -(1 / 2)) (by norm_num)
  have h₂ := Gamma_add_one (s := 1 / 2) (by norm_num)
  norm_num at h₀ h₁ h₂
  linarith

end Real
