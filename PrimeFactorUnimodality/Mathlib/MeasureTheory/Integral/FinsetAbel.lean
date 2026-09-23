/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Abel summation for finitely many real locations

Finite weighted atoms at arbitrary real locations admit summation by parts
against their cumulative counting function. Labels need not have distinct
locations: repeated locations retain their multiplicity. Unlike the
natural-indexed Abel formula, no integrality assumption is imposed on the
locations. The proof integrates the indicator for each atom and uses the
fundamental theorem of calculus.
-/

noncomputable section

open MeasureTheory Set

namespace Finset

variable {ι : Type*} {a b : ℝ} {f g : ℝ → ℝ}

/-- The cumulative weight times an integrable function is integrable. -/
theorem integrableOn_sum_filter_mul (s : Finset ι) (r c : ι → ℝ)
    (hg : IntegrableOn g (Set.Icc a b)) :
    IntegrableOn (fun x => (∑ i ∈ s with r i ≤ x, c i) * g x) (Set.Icc a b) := by
  classical
  have hi (i : ι) : IntegrableOn ((Set.Ici (r i)).indicator (fun x => c i * g x))
      (Set.Icc a b) :=
    (hg.const_mul (c i)).indicator measurableSet_Ici
  apply (integrable_finsetSum s (fun i _ => hi i)).congr
  filter_upwards [] with x
  rw [Finset.sum_filter, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : r i ≤ x <;> simp [hx]

/-- Weighted Abel summation on a finite set whose locations lie in the interval. -/
theorem sum_mul_eq_sum_mul_sub_integral_count (s : Finset ι) (r c : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc a b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (g x) x)
    (hg : IntegrableOn g (Set.Icc a b)) :
    ∑ i ∈ s, c i * f (r i) = (∑ i ∈ s, c i) * f b -
      ∫ x in Set.Icc a b, (∑ i ∈ s with r i ≤ x, c i) * g x := by
  classical
  have he (i : ι) (hi : i ∈ s) :
      (∫ x in Set.Icc a b, (Set.Ici (r i)).indicator (fun x => c i * g x) x) =
        c i * (f b - f (r i)) := by
    rw [setIntegral_indicator measurableSet_Ici]
    have hs : Set.Icc a b ∩ Set.Ici (r i) = Set.Icc (r i) b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(hr i hi).1.trans h.1, h.2⟩, h.1⟩⟩
    rw [hs, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hr i hi).2]
    congr 1
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le (hr i hi).2] at hx
      exact hf x ⟨(hr i hi).1.trans hx.1, hx.2⟩
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le (hr i hi).2).mpr
        (hg.mono_set (Set.Icc_subset_Icc (hr i hi).1 le_rfl))
  have hsum : (fun x => (∑ i ∈ s with r i ≤ x, c i) * g x) =
      fun x => ∑ i ∈ s, (Set.Ici (r i)).indicator (fun y => c i * g y) x := by
    funext x
    rw [Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : r i ≤ x <;> simp [hx]
  rw [hsum, integral_finsetSum s
    (fun i _ => (hg.const_mul (c i)).indicator measurableSet_Ici), Finset.sum_congr rfl he]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  ring

/-- The finite cumulative count is integrable on every compact interval. -/
theorem integrableOn_count_le (s : Finset ι) (r : ι → ℝ) :
    IntegrableOn (fun x => ((s.filter (fun i => r i ≤ x)).card : ℝ)) (Set.Icc a b) := by
  have h := integrableOn_sum_filter_mul s r (fun _ => (1 : ℝ))
    (continuous_const.integrableOn_Icc :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b))
  simpa using h

/-- Integrate a finite count, clipping early locations and retaining repeated labels. -/
theorem integral_count_le_eq_sum_sub_max (s : Finset ι) (r : ι → ℝ) (hab : a ≤ b)
    (hr : ∀ i ∈ s, r i ≤ b) :
    (∫ x in Set.Icc a b, ((s.filter (fun i => r i ≤ x)).card : ℝ)) =
      ∑ i ∈ s, (b - max a (r i)) := by
  classical
  have h := sum_mul_eq_sum_mul_sub_integral_count s (fun i => max a (r i)) (fun _ => (1 : ℝ))
    (fun i hi => ⟨le_max_left _ _, max_le hab (hr i hi)⟩)
    (fun x _ => hasDerivAt_id x)
    (continuous_const.integrableOn_Icc :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b))
  simp only [one_mul, sum_const, nsmul_eq_mul, mul_one, id_eq] at h
  have hi : (∫ x in Set.Icc a b,
      ((s.filter (fun i => max a (r i) ≤ x)).card : ℝ)) =
      ∫ x in Set.Icc a b, ((s.filter (fun i => r i ≤ x)).card : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    have he : s.filter (fun i => max a (r i) ≤ x) = s.filter (fun i => r i ≤ x) :=
      filter_congr (fun _ _ => max_le_iff.trans (and_iff_right hx.1))
    exact congrArg (fun v : Finset ι => (v.card : ℝ)) he
  rw [hi] at h
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith only [h]

end Finset
