import PrimeFactorUnimodality.Mathlib.Algebra.BigOperators.Ring.Horner

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open List

example {R : Type*} [Semiring R]
    (a : ℕ → R) (x : R) (start count : ℕ) :
    ((List.range' start count).map a).foldr (fun c v => c + v * x) 0 =
      ∑ j ∈ Finset.range count, a (start + j) * x ^ j := by
  exact List.foldr_horner_range' a x start count

example : ((List.range' 2 3).map (fun j : ℕ => j)).foldr (fun c v => c + v * 2) 0 = 24 :=
  by decide
example (a : ℕ → ℕ) : ((List.range' 5 0).map a).foldr (fun c v => c + v * 3) 0 = 0 := rfl

end

end PrimeFactorUnimodality.Tests
