import PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSievePrimeLeaves

/-! # PartialSievePrimeLeaves: semantic and boundary regression tests -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Finset
open PrimeFactorUnimodality


example (n y : ℕ) : Nat.Coprime n (primorial y) ↔
    ∀ p, p.Prime → p ≤ y → ¬p ∣ n := Nat.coprime_primorial_iff n y
example {n y : ℕ} (hn : 1 ≤ n) (hy : y ≤ n) (hsq : n < (y + 1) ^ 2) :
    Nat.coprimeCount (primorial y) n = Nat.primeCounting n - Nat.primeCounting y + 1 :=
  Nat.coprimeCount_primorial_eq hn hy hsq
example : Nat.primeCounting 100 = 25 := by
  have h := Nat.primeCounting_eq_of_partialSieveCount (ps := [2, 3, 5, 7])
    (n := 100) (y := 10) (c := 22) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  exact h
example : Nat.coprimeCount (primorial 2) 9 = 5 ∧
    Nat.primeCounting 9 - Nat.primeCounting 2 + 1 = 4 := by decide +kernel
example : Nat.coprimeCount (primorial 2) 8 = 4 := by decide +kernel
example : Nat.coprimeCount (primorial 0) 0 = 0 := by decide +kernel

end PrimeFactorUnimodality.Tests
