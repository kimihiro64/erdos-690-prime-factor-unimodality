import PrimeFactorUnimodality.Helpers.Analytic.MomentIntervalColumns

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality.ComplexInterval

variable {degree : ℕ}

example (w : ℂ) (r : ℝ) (degree : ℕ)
    {W : ComplexInterval} {R : IntervalRat} (hw : w ∈ W) (hr : r ∈ R)
    (j : Fin degree) :
    w * (I * (r : ℂ)) ^ j.val / (j.val.factorial : ℂ) ∈
      (momentVector W R degree)[j.val] := by
  exact PrimeFactorUnimodality.ComplexInterval.momentVector_sound w r degree hw hr j

example {α : Type*} {degree : ℕ} (rows : List α)
    (value : α → ℂ) (enclosure : α → Vector ComplexInterval degree) (j : Fin degree)
    (h : ∀ a ∈ rows, value a ∈ (enclosure a)[j.val]) :
    (rows.map value).sum ∈ (sumVectors (rows.map enclosure))[j.val] := by
  exact PrimeFactorUnimodality.ComplexInterval.sumVectors_sound rows value enclosure j h

example : momentVector (point ⟨1, 0⟩) (IntervalRat.singleton 0) 0 = #v[] := by decide +kernel
example : sumVectors [#v[point ⟨2, 0⟩], #v[point ⟨3, 0⟩]] = #v[point ⟨5, 0⟩] := by decide +kernel

end

end PrimeFactorUnimodality.Tests
