import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixTwo

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Fourier

variable {R : Type*} [CommSemiring R]

example (w : R) (n : ℕ) (i : Fin (n + 1)) :
    (powerTable w n)[i.val] = w ^ i.val := by
  exact Fourier.powerTable_get w n i

example (n : ℕ) (f : Fin (n * 2) → R) :
    (∑ i, f i) =
      (∑ i : Fin n, f ⟨2 * i.val, by have := i.isLt; omega⟩) +
        ∑ i : Fin n, f ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
  exact Fourier.sum_fin_double n f

example (n : ℕ) (w : R) (hw : w ^ (2 ^ n) = 1)
    (a : Vector R (2 ^ n)) (k : Fin (2 ^ n)) :
    (radixTwo n w a)[k.val] = ∑ j : Fin (2 ^ n), a[j.val] * w ^ (k.val * j.val) := by
  exact Fourier.radixTwo_get n w hw a k

example (n : ℕ) : radixTwoMergeCount n = n * 2 ^ n := by
  exact Fourier.radixTwoMergeCount_eq n

example : powerTable (2 : ℕ) 3 = #v[1, 2, 4, 8] := by decide

example : radixTwo 0 (1 : ℕ) #v[7] = #v[7] := by decide

example : radixTwo 2 (1 : ℕ) #v[1, 2, 3, 4] = #v[10, 10, 10, 10] := by decide

example : radixTwo 2 (-1 : ℤ) #v[1, 2, 3, 4] = #v[10, -2, 10, -2] := by decide

example : radixTwoMergeCount 3 = 24 := by decide

end

end PrimeFactorUnimodality.Tests
