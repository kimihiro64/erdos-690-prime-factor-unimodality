/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.ProjIcc

/-! # A continuous logarithm along a nonvanishing closed interval

Extend the function constantly past its endpoints using `projIcc`, then use
Mathlib's lifting theorem for the exponential covering. The initial logarithm
is prescribed, and no choice of the discontinuous principal argument is made
along the interval. Degenerate intervals are included.
-/

open Set

namespace Complex

/-- A continuous nonvanishing function on a real interval has a continuous logarithm
with any prescribed initial value exponentiating to the initial function value. -/
theorem exists_continuous_log_on_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hne : ∀ x ∈ Icc a b, f x ≠ 0)
    {z₀ : ℂ} (hz₀ : exp z₀ = f a) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L a = z₀ ∧ ∀ x ∈ Icc a b, exp (L x) = f x := by
  let G : C(ℝ, ℂ) := ⟨fun x => f (projIcc a b hab x),
    (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc⟩
  have hG (x : ℝ) (hx : x ∈ Icc a b) : G x = f x := by
    change f (projIcc a b hab x) = f x
    rw [projIcc_of_mem hab hx]
  obtain ⟨L, ⟨hLa, hL⟩, _⟩ := isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    G (a₀ := a) (hz₀.trans (hG a ⟨le_rfl, hab⟩).symm)
    (fun x => hne _ (projIcc a b hab x).property)
  refine ⟨L, L.continuous, hLa, ?_⟩
  intro x hx
  exact (congrFun hL x).trans (hG x hx)

end Complex
