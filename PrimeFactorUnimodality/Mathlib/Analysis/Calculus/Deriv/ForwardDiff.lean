/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Linarith

/-! # Analytic bounds for the existing forward-difference operator

Nonnegative steps preserve a half-line. Differentiation commutes with
every iterated forward difference there, and a bound on its finite support
gives the explicit norm bound `2^n` times that bound.
-/

open Function Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Nonnegative forward steps preserve continuity on a half-line. -/
theorem continuousOn_fwdDiff_iter_Ici {a h : ℝ} (hh : 0 ≤ h)
    {f : ℝ → E} (hf : ContinuousOn f (Ici a)) (n : ℕ) :
    ContinuousOn ((fwdDiff h)^[n] f) (Ici a) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [iterate_succ_apply']
    exact (ih.comp (continuous_id.add_const h).continuousOn
      (fun x hx => show a ≤ x + h from hx.trans (le_add_of_nonneg_right hh))).sub ih

/-- Differentiation commutes with every forward difference on a half-line. -/
theorem hasDerivAt_fwdDiff_iter_Ici {a h : ℝ} (hh : 0 ≤ h)
    {f g : ℝ → E} (hf : ∀ x ∈ Ici a, HasDerivAt f (g x) x) (n : ℕ)
    {x : ℝ} (hx : a ≤ x) :
    HasDerivAt ((fwdDiff h)^[n] f) (((fwdDiff h)^[n] g) x) x := by
  induction n generalizing x with
  | zero => exact hf x hx
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    change HasDerivAt (fun t => ((fwdDiff h)^[n] f) (t + h) - ((fwdDiff h)^[n] f) t)
      (((fwdDiff h)^[n] g) (x + h) - ((fwdDiff h)^[n] g) x) x
    have hp := (ih (x := x + h) (by linarith)).scomp x ((hasDerivAt_id x).add_const h)
    simpa only [Function.comp_def, Pi.sub_def, id_eq, one_smul] using hp.sub (ih hx)

omit [NormedSpace ℝ E] in
/-- A uniform bound on the difference's finite support gives a `2^n` norm bound. -/
theorem norm_fwdDiff_iter_le {h x C : ℝ} (hh : 0 ≤ h) (n : ℕ) {f : ℝ → E}
    (hbound : ∀ t ∈ Icc x (x + n * h), ‖f t‖ ≤ C) :
    ‖((fwdDiff h)^[n] f) x‖ ≤ 2 ^ n * C := by
  induction n generalizing x with
  | zero => simpa using hbound x (by simp)
  | succ n ih =>
    rw [iterate_succ_apply']
    change ‖((fwdDiff h)^[n] f) (x + h) - ((fwdDiff h)^[n] f) x‖ ≤ _
    have hlo := ih (x := x) (by
      intro t ht
      apply hbound t
      constructor
      · exact ht.1
      · push_cast
        linarith [ht.2])
    have hhi := ih (x := x + h) (by
      intro t ht
      apply hbound t
      constructor
      · linarith [ht.1]
      · push_cast
        linarith [ht.2])
    calc
      _ ≤ ‖((fwdDiff h)^[n] f) (x + h)‖ + ‖((fwdDiff h)^[n] f) x‖ := norm_sub_le _ _
      _ ≤ 2 ^ n * C + 2 ^ n * C := add_le_add hhi hlo
      _ = 2 ^ (n + 1) * C := by rw [pow_succ]; ring
