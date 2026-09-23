import PrimeFactorUnimodality.Helpers.Analytic.ComplexPolynomialIntervals

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.ComplexInterval

example {x : ℂ} {X : ComplexInterval} (hx : x ∈ X)
    {values : List ℂ} {coefficients : List ComplexInterval}
    (h : List.Forall₂ (fun z J => z ∈ J) values coefficients) :
    values.foldr (fun a b => a + b * x) 0 ∈ horner X coefficients := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_horner hx h

example {x : ℂ} {X : ComplexInterval} (hx : x ∈ X)
    (weight : ℕ → ℂ) (coefficient : ℕ → ComplexInterval) (start count : ℕ)
    (h : ∀ n ∈ List.range' start count, weight n ∈ coefficient n) :
    (∑ j ∈ range count, weight (start + j) * x ^ j) ∈
      polynomial X coefficient start count := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_polynomial hx weight coefficient start count h

example : horner (point ⟨0, 1⟩) [point ⟨1, 0⟩, point ⟨2, 0⟩] = point ⟨1, 2⟩ :=
  by decide +kernel
example : horner (point ⟨1, 2⟩) [] = point ⟨0, 0⟩ := rfl
example : polynomial (point ⟨2, 0⟩) (fun j => point ⟨j, 0⟩) 2 3 = point ⟨24, 0⟩ :=
  by decide +kernel

end

end PrimeFactorUnimodality.Tests
