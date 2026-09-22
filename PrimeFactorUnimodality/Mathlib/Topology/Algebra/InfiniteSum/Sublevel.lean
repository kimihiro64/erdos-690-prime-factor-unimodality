/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Summable real-location series and finite sublevel counts

Finite sublevels exhaust a summable series. If its weights come from a
nonnegative decreasing function tending to zero, the sublevel cardinality
times the weight at the cutoff also tends to zero. The latter uses
dominated convergence for series, not a quantitative counting estimate.
Repeated locations remain separate indices.
-/

open Filter Set
open scoped Topology

namespace Summable

variable {ι : Type*} {r : ι → ℝ}

/-- Summation over finite real sublevels converges to the whole series. -/
theorem tendsto_sum_sublevel {f : ι → ℝ} (hf : Summable f)
    (hfin : ∀ T, {i | r i ≤ T}.Finite) :
    Tendsto (fun T => ∑ i ∈ (hfin T).toFinset, f i) atTop (𝓝 (∑' i, f i)) := by
  have hmono : Monotone (fun T => (hfin T).toFinset) := by
    intro a b hab i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi ⊢
    exact hi.trans hab
  exact hf.hasSum.comp (hmono.tendsto_atTop_finset (fun i => ⟨r i, by simp⟩))

/-- A decreasing summable weight kills its counting boundary at infinity. -/
theorem tendsto_card_sublevel_mul_of_antitone {a : ℝ} {f : ℝ → ℝ}
    (hs : Summable (fun i => f (r i))) (hr : ∀ i, a < r i)
    (hfin : ∀ T, {i | r i ≤ T}.Finite)
    (hpos : ∀ x ∈ Ioi a, 0 ≤ f x) (hmono : AntitoneOn f (Ioi a))
    (hzero : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun T => ((hfin T).toFinset.card : ℝ) * f T) atTop (𝓝 0) := by
  classical
  let F (T : ℝ) (i : ι) := if r i ≤ T then f T else 0
  have hpoint (i : ι) : Tendsto (fun T => F T i) atTop (𝓝 0) := by
    apply hzero.congr'
    filter_upwards [eventually_ge_atTop (r i)] with T hT
    simp [F, hT]
  have hbound : ∀ᶠ T in atTop, ∀ i, ‖F T i‖ ≤ f (r i) := by
    filter_upwards [eventually_gt_atTop a] with T hT i
    by_cases hi : r i ≤ T
    · simpa only [F, ite_eq_left hi, Real.norm_eq_abs, abs_of_nonneg (hpos T hT)] using
        hmono (hr i) hT hi
    · simpa only [F, ite_eq_right hi, norm_zero] using hpos (r i) (hr i)
  have h := tendsto_tsum_of_dominated_convergence hs hpoint hbound
  have he (T : ℝ) : (∑' i, F T i) = ((hfin T).toFinset.card : ℝ) * f T := by
    rw [tsum_eq_sum (s := (hfin T).toFinset)
      (fun i hi => by
        have hn : ¬r i ≤ T := fun h => hi ((hfin T).mem_toFinset.mpr h)
        simp [F, hn])]
    calc
      _ = ∑ _i ∈ (hfin T).toFinset, f T := by
        apply Finset.sum_congr rfl
        intro i hi
        exact ite_eq_left (show r i ≤ T from (hfin T).mem_toFinset.mp hi)
      _ = _ := by simp
  simpa only [he, tsum_zero] using h

end Summable
