import PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSieve

/-! # PartialSieve: semantic and boundary regression tests -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Finset
open PrimeFactorUnimodality


example (n : ℕ) : Nat.coprimeCount 1 n = n := Nat.coprimeCount_one n
example (m : ℕ) : Nat.coprimeCount m 0 = 0 := Nat.coprimeCount_zero m
example (m n : ℕ) {p : ℕ} (hp : p.Prime) (hc : Nat.Coprime p m) :
    Nat.coprimeCount (m * p) n + Nat.coprimeCount m (n / p) = Nat.coprimeCount m n :=
  Nat.coprimeCount_mul_prime_add m n hp hc
example {p q : ℕ → ℕ} {a : ℕ} (h : ∀ i < a, p i = q i) (n : ℕ) :
    Nat.sievePhi p a n = Nat.sievePhi q a n := Nat.sievePhi_congr h n
example : Nat.partialSieveCount [2, 3, 5] 100 = 26 := by decide +kernel
example : Nat.partialSieveCount [5, 3, 2] 100 = 26 := by decide +kernel
example : Nat.coprimeCount 30 100 = 26 :=
  (Nat.partialSieveCount_eq [2, 3, 5] (by decide) (by decide) 100).symm.trans
    (by decide +kernel)
example : Nat.partialSieveCount [2, 2] 4 = 1 ∧ Nat.coprimeCount 4 4 = 2 := by
  decide +kernel
example : Nat.partialSieveCount [4] 8 = 6 ∧ Nat.coprimeCount 4 8 = 4 := by
  decide +kernel

end PrimeFactorUnimodality.Tests
