import Mathlib.Data.List.Forall2
import PrimeFactorUnimodality.Helpers.Analytic.MomentIntervalRecurrence

/-! # Materialized moment columns and reusable interval sum assembly

Convert each atom's recurrence to one shared array. Sum those arrays once
per chunk, with one theorem establishing all column enclosures. No separate
transcendental evaluation is needed for different moment orders.
-/

namespace PrimeFactorUnimodality.ComplexInterval

open Complex LeanCert.Core

/-- Materialize the initial segment of a shared moment recurrence as an array. -/
def momentVector (W : ComplexInterval) (R : IntervalRat) (degree : ℕ) :
    Vector ComplexInterval degree :=
  ⟨(moments W R 0 degree).toArray, by simp [length_moments]⟩

/-- Every materialized column encloses the exact Taylor atom. -/
theorem momentVector_sound (w : ℂ) (r : ℝ) (degree : ℕ)
    {W : ComplexInterval} {R : IntervalRat} (hw : w ∈ W) (hr : r ∈ R)
    (j : Fin degree) :
    w * (I * (r : ℂ)) ^ j.val / (j.val.factorial : ℂ) ∈
      (momentVector W R degree)[j.val] := by
  have h := moments_sound w r 0 degree (by simpa using hw) hr
  have h₁ : j.val < ((List.range' 0 degree).map
      (fun k => w * (I * (r : ℂ)) ^ k / (k.factorial : ℂ))).length := by
    simpa using j.isLt
  have h₂ : j.val < (moments W R 0 degree).length := by
    simpa [length_moments] using j.isLt
  simpa [momentVector, List.get_eq_getElem] using h.get h₁ h₂

/-- Shared componentwise assembly, including the empty chunk. -/
def sumVectors {degree : ℕ} : List (Vector ComplexInterval degree) →
    Vector ComplexInterval degree
  | [] => Vector.replicate degree (point ⟨0, 0⟩)
  | row :: rows => Vector.zipWith add row (sumVectors rows)

/-- Any exact values enclosed by the input rows remain enclosed by the assembled column. -/
theorem sumVectors_sound {α : Type*} {degree : ℕ} (rows : List α)
    (value : α → ℂ) (enclosure : α → Vector ComplexInterval degree) (j : Fin degree)
    (h : ∀ a ∈ rows, value a ∈ (enclosure a)[j.val]) :
    (rows.map value).sum ∈ (sumVectors (rows.map enclosure))[j.val] := by
  induction rows with
  | nil =>
    simp only [List.map_nil, List.sum_nil, sumVectors, Vector.getElem_replicate]
    constructor <;> norm_num [point, IntervalRat.mem_def, IntervalRat.singleton]
  | cons a rows ih =>
    simp only [List.map_cons, List.sum_cons, sumVectors, Vector.getElem_zipWith]
    exact mem_add (h a (by simp)) (ih (fun a ha => h a (by simp [ha])))

end PrimeFactorUnimodality.ComplexInterval
