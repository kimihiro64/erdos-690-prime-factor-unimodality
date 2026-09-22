/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Circle averages from antipodal bounds

Pairing opposite points turns complementary semicircle estimates into
an average estimate. No measurable partition or choice of argument is
needed: negating the radius is already measure preserving.
-/

open Complex Metric

namespace Real

/-- Reflection through the centre preserves the circle average. -/
theorem circleAverage_map_antipode {f : ℂ → ℝ} {c : ℂ} {R : ℝ} :
    circleAverage (fun z => f (2 * c - z)) c R = circleAverage f c R := by
  have he (θ : ℝ) : 2 * c - circleMap c R θ = circleMap c (-R) θ := by
    simp only [circleMap, Complex.ofReal_neg]
    ring
  calc
    _ = circleAverage f c (-R) := by simp only [circleAverage, he]
    _ = _ := circleAverage_neg_radius

/-- Integrability is preserved by the antipodal reflection. -/
theorem circleIntegrable_map_antipode {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) : CircleIntegrable (fun z => f (2 * c - z)) c R := by
  have he (θ : ℝ) : 2 * c - circleMap c R θ = circleMap c (-R) θ := by
    simp only [circleMap, Complex.ofReal_neg]
    ring
  change IntervalIntegrable (fun θ => f (2 * c - circleMap c R θ)) _ _ _
  simp only [he]
  exact circleIntegrable_neg_radius.mpr hf

/-- An upper bound for every antipodal pair bounds the full circle average by half as much. -/
theorem circleAverage_le_of_antipodal_bound {f : ℂ → ℝ} {c : ℂ} {R B : ℝ}
    (hf : CircleIntegrable f c R)
    (hb : ∀ z ∈ sphere c |R|, f z + f (2 * c - z) ≤ B) :
    circleAverage f c R ≤ B / 2 := by
  have h := circleAverage_mono_on_of_le_circle (hf.add (circleIntegrable_map_antipode hf)) hb
  rw [circleAverage_add hf (circleIntegrable_map_antipode hf), circleAverage_map_antipode] at h
  linarith

end Real
