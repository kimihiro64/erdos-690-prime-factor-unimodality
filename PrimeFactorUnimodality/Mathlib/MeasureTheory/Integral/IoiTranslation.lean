/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Translation of improper integrals on open upper intervals

Specialize the existing measure-preserving translation API to `(H,infinity)`.
No integrability assumption is required for the integral equality; a separate
equivalence transports actual integrability when it is available.
-/

namespace MeasureTheory

open Set

variable {E : Type*} [NormedAddCommGroup E]

/-- Translating both integrand and lower endpoint preserves improper integrability. -/
theorem integrableOn_Ioi_comp_add_iff (t H : ℝ) (f : ℝ → E) :
    IntegrableOn (fun x => f (x + t)) (Ioi H) ↔ IntegrableOn f (Ioi (H + t)) := by
  have hp : (fun x : ℝ => x + t) ⁻¹' Ioi (H + t) = Ioi H := by
    ext x
    simp
  have h := (measurePreserving_add_right (volume : Measure ℝ) t).integrableOn_comp_preimage
    (MeasurableEquiv.addRight t).measurableEmbedding (f := f) (s := Ioi (H + t))
  simpa only [hp, Function.comp_def] using h

/-- Translation moves the lower endpoint of the improper integral by the same amount. -/
theorem integral_Ioi_comp_add [NormedSpace ℝ E] (t H : ℝ) (f : ℝ → E) :
    (∫ x in Ioi H, f (x + t)) = ∫ x in Ioi (H + t), f x := by
  have hp : (fun x : ℝ => x + t) ⁻¹' Ioi (H + t) = Ioi H := by
    ext x
    simp
  have h := (measurePreserving_add_right (volume : Measure ℝ) t).restrict_preimage_emb
    (MeasurableEquiv.addRight t).measurableEmbedding (Ioi (H + t))
  rw [hp] at h
  exact h.integral_comp (MeasurableEquiv.addRight t).measurableEmbedding f

end MeasureTheory
