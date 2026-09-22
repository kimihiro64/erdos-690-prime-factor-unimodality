/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Endpoint minima when derivative nonpositivity persists

If a differentiable real function's derivative cannot turn positive after
being nonpositive, its value on an interval is at least the smaller
endpoint value. No global monotonicity or concavity is required.
-/

namespace Real

/-- A derivative that never returns to positive values excludes a strict interior minimum. -/
theorem min_endpoints_le_of_deriv_nonpos_persistent {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hpersist : ∀ x y, x ≤ y → f' x ≤ 0 → f' y ≤ 0)
    {l r w : ℝ} (hw : w ∈ Set.Icc l r) : min (f l) (f r) ≤ f w := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  by_cases hsign : f' w ≤ 0
  · have hm : AntitoneOn f (Set.Icc w r) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc w r) hc.continuousOn
        (fun x _ => (hf x).hasDerivWithinAt) (fun x hx =>
          hpersist w x (interior_subset hx).1 hsign)
    exact (min_le_right _ _).trans (hm ⟨le_rfl, hw.2⟩ ⟨hw.2, le_rfl⟩ hw.2)
  · have hm : MonotoneOn f (Set.Icc l w) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l w) hc.continuousOn
        (fun x _ => (hf x).hasDerivWithinAt) (fun x hx => by
          by_contra hn
          exact hsign (hpersist x w (interior_subset hx).2 (le_of_lt (lt_of_not_ge hn))))
    exact (min_le_left _ _).trans (hm ⟨le_rfl, hw.1⟩ ⟨hw.1, le_rfl⟩ hw.1)

end Real
