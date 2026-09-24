/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # A factorial Taylor remainder bound for either direction

The vector-valued integral remainder and the exact integral of the absolute
polynomial weight give the factor `(n+1)!`. The center may lie on either
side of the evaluation point. No real-valued mean-value remainder is used.
-/

open MeasureTheory Set
open scoped ContDiff Interval Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The factorial Taylor remainder bound for a Banach-valued function on a real segment. -/
theorem norm_sub_sum_taylor_le {f : ℝ → E} {n : ℕ} {a x C : ℝ}
    (hf : ContDiff ℝ (n + 1 : ℕ) f)
    (hC : ∀ y ∈ uIcc a x, ‖iteratedDeriv (n + 1) f y‖ ≤ C) :
    ‖f x - ∑ k ∈ Finset.range (n + 1), ((x - a) ^ k / (k ! : ℝ)) • iteratedDeriv k f a‖ ≤
      C * |x - a| ^ (n + 1) / ((n + 1)! : ℝ) := by
  by_cases hax : a = x
  · subst x
    have hs : (∑ k ∈ Finset.range (n + 1),
        ((a - a) ^ k / (k ! : ℝ)) • iteratedDeriv k f a) = f a := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp [zero_pow hk0]
      · simp
    rw [hs]
    simp
  have hu := uniqueDiffOn_uIcc hax
  have hd (k : ℕ) (hk : k ≤ n + 1) (y : ℝ) (hy : y ∈ uIcc a x) :
      iteratedDerivWithin k f (uIcc a x) y = iteratedDeriv k f y :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hf.contDiffAt.of_le (by exact_mod_cast hk)) hy
  have hp : taylorWithinEval f n (uIcc a x) a x =
      ∑ k ∈ Finset.range (n + 1), ((x - a) ^ k / (k ! : ℝ)) • iteratedDeriv k f a := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hd k (by have := Finset.mem_range.mp hk; omega) a (left_mem_uIcc)]
    congr 1
    ring
  rw [← hp, taylor_integral_remainder hf.contDiffOn,
    intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  have hg : IntegrableOn (fun t : ℝ => C / (n ! : ℝ) * |x - t| ^ n) (Ι a x) := by
    have hc : Continuous (fun t : ℝ => C / (n ! : ℝ) * |x - t| ^ n) := by fun_prop
    exact (hc.intervalIntegrable a x).def'
  calc
    _ ≤ ∫ t in Ι a x, C / (n ! : ℝ) * |x - t| ^ n := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      have ht' := uIoc_subset_uIcc ht
      rw [hd (n + 1) le_rfl t ht', norm_smul, Real.norm_eq_abs, abs_div,
        abs_pow, Nat.abs_cast]
      calc
        _ ≤ (|x - t| ^ n / (n ! : ℝ)) * C :=
          mul_le_mul_of_nonneg_left (hC t ht') (by positivity)
        _ = _ := by ring
    _ = C / (n ! : ℝ) * (|x - a| ^ (n + 1) / (n + 1)) := by
      rw [integral_const_mul]
      congr 1
      simpa only [uIoc_comm, abs_sub_comm] using
        (integral_pow_abs_sub_uIoc (a := x) (b := a) (n := n))
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
