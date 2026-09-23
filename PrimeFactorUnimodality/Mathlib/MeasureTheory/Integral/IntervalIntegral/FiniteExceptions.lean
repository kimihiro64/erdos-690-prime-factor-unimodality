/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-! # Fundamental theorem of calculus with finitely many exceptional points

Continuity at the exceptional points allows adjacent primitive increments
to telescope. Induction splits at each interior exception; exceptions at
the endpoints or outside the interval require no derivative hypothesis.
Unlike an almost-everywhere derivative assertion alone, these assumptions
suffice for the fundamental theorem of calculus.
-/

open MeasureTheory Set

namespace intervalIntegral

/-- A continuous primitive with an integrable derivative off a finite set satisfies FTC. -/
theorem integral_eq_sub_of_hasDerivAt_off_finset {f f' : ℝ → ℝ} (s : Finset ℝ)
    {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a b) :
    (∫ x in a..b, f' x) = f b - f a := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
    exact integral_eq_sub_of_hasDerivAt_of_le hab hc (fun x hx => hd x hx (by simp)) hi
  | @insert c s hcs ih =>
    by_cases hcab : c ∈ Ioo a b
    · have hil : IntervalIntegrable f' volume a c := hi.mono_set (by
        rw [uIcc_of_le hcab.1.le, uIcc_of_le hab]
        exact Icc_subset_Icc le_rfl hcab.2.le)
      have hir : IntervalIntegrable f' volume c b := hi.mono_set (by
        rw [uIcc_of_le hcab.2.le, uIcc_of_le hab]
        exact Icc_subset_Icc hcab.1.le le_rfl)
      have hl := ih hcab.1.le (hc.mono (Icc_subset_Icc le_rfl hcab.2.le))
        (fun x hx hxs => hd x ⟨hx.1, hx.2.trans hcab.2⟩
          (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hxs⟩)) hil
      have hr := ih hcab.2.le (hc.mono (Icc_subset_Icc hcab.1.le le_rfl))
        (fun x hx hxs => hd x ⟨hcab.1.trans hx.1, hx.2⟩
          (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hxs⟩)) hir
      rw [← integral_add_adjacent_intervals hil hir, hl, hr]
      ring
    · apply ih hab hc _ hi
      intro x hx hxs
      apply hd x hx
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun he => hcab (he ▸ hx), hxs⟩

end intervalIntegral
