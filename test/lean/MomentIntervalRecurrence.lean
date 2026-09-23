import PrimeFactorUnimodality.Helpers.Analytic.MomentIntervalRecurrence

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality.ComplexInterval

variable {degree : ℕ}

example (w : ℂ) (r : ℝ) (j : ℕ) {W : ComplexInterval} {R : IntervalRat}
    (hw : w * (I * (r : ℂ)) ^ j / (j.factorial : ℂ) ∈ W) (hr : r ∈ R) :
    w * (I * (r : ℂ)) ^ (j + 1) / ((j + 1).factorial : ℂ) ∈ momentStep W R j := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_momentStep w r j hw hr

example (w : ℂ) (r : ℝ) (start count : ℕ)
    {W : ComplexInterval} {R : IntervalRat}
    (hw : w * (I * (r : ℂ)) ^ start / (start.factorial : ℂ) ∈ W) (hr : r ∈ R) :
    List.Forall₂ (fun z J => z ∈ J)
      ((List.range' start count).map (fun j => w * (I * (r : ℂ)) ^ j / (j.factorial : ℂ)))
      (moments W R start count) := by
  exact PrimeFactorUnimodality.ComplexInterval.moments_sound w r start count hw hr

example (W : ComplexInterval) (R : IntervalRat) (start count : ℕ) :
    (moments W R start count).length = count := by
  exact PrimeFactorUnimodality.ComplexInterval.length_moments W R start count

example (w z : ℂ) (j : ℕ) :
    w * z ^ (j + 1) / ((j + 1).factorial : ℂ) =
      (w * z ^ j / (j.factorial : ℂ)) * z / (j + 1 : ℂ) := taylorMoment_succ w z j
example : moments (point ⟨1, 0⟩) (IntervalRat.singleton 1) 0 4 =
    [point ⟨1, 0⟩, point ⟨0, 1⟩, point ⟨-1 / 2, 0⟩, point ⟨0, -1 / 6⟩] := by decide +kernel

end

end PrimeFactorUnimodality.Tests
