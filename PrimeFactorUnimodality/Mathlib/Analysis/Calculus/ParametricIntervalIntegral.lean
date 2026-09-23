/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

/-! # Differentiation under a finite integral on a compact rectangle

Joint continuity of a function and its parameter derivative on a closed
rectangle supplies the uniform integrable majorant required by Mathlib's
dominated differentiation theorem. The integration endpoints may coincide
or be reversed.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace intervalIntegral

/-- A continuous parameter derivative on a compact rectangle can be integrated. -/
theorem hasDerivAt_integral_of_continuousOn_rectangle
    {F F' : ℝ → ℝ → ℝ} {a b t r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn (Function.uncurry F) (Icc (t - r) (t + r) ×ˢ uIcc a b))
    (hF' : ContinuousOn (Function.uncurry F') (Icc (t - r) (t + r) ×ˢ uIcc a b))
    (hd : ∀ u ∈ Ioo (t - r) (t + r), ∀ x ∈ uIcc a b,
      HasDerivAt (fun v => F v x) (F' u x) u) :
    HasDerivAt (fun u => ∫ x in a..b, F u x) (∫ x in a..b, F' t x) t := by
  have ht : t ∈ Ioo (t - r) (t + r) := ⟨by linarith, by linarith⟩
  have hslice {G : ℝ → ℝ → ℝ}
      (hG : ContinuousOn (Function.uncurry G) (Icc (t - r) (t + r) ×ˢ uIcc a b))
      {u : ℝ} (hu : u ∈ Icc (t - r) (t + r)) : ContinuousOn (G u) (uIcc a b) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨hu, hx⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hF'
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
    ?_ (hslice hF ⟨ht.1.le, ht.2.le⟩).intervalIntegrable
    ?_ ?_ (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b) ?_).2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact ((hslice hF ⟨hu.1.le, hu.2.le⟩).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact ((hslice hF' ⟨ht.1.le, ht.2.le⟩).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact Filter.Eventually.of_forall (fun x hx u hu =>
      hC (u, x) ⟨⟨hu.1.le, hu.2.le⟩, uIoc_subset_uIcc hx⟩)
  · exact Filter.Eventually.of_forall (fun x hx u hu => hd u hu x (uIoc_subset_uIcc hx))

end intervalIntegral
