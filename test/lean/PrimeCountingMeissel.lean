import PrimeFactorUnimodality.Mathlib.NumberTheory.PrimeCountingMeissel

/-! # PrimeCountingMeissel: semantic and boundary regression tests -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Finset
open PrimeFactorUnimodality


example (a : ℕ) : Nat.primesBelow (Nat.nth Nat.Prime a) =
    (range a).image (Nat.nth Nat.Prime) := Nat.primesBelow_nth_prime a
example (a : ℕ) : (∏ i ∈ range a, Nat.nth Nat.Prime i) =
    primorial (Nat.nth Nat.Prime a - 1) := Nat.prod_nth_prime_eq_primorial a
example {a b : ℕ} (hab : a ≤ b) (n : ℕ) :
    Nat.sievePhi (Nat.nth Nat.Prime) a n = Nat.sievePhi (Nat.nth Nat.Prime) b n +
      ∑ i ∈ Ico a b, Nat.sievePhi (Nat.nth Nat.Prime) i (n / Nat.nth Nat.Prime i) :=
  Nat.sievePhi_nth_prime_telescope hab n
example {n a b : ℕ} (hab : a ≤ b) (hn : 1 ≤ n)
    (hb : Nat.nth Nat.Prime b - 1 ≤ n) (hsq : n < Nat.nth Nat.Prime b ^ 2)
    (hcube : n < Nat.nth Nat.Prime a ^ 3)
    (hsquares : ∀ i ∈ Ico a b, Nat.nth Nat.Prime i ^ 2 ≤ n) :
    Nat.primeCounting n = Nat.sievePhi (Nat.nth Nat.Prime) a n + b - 1 -
      ∑ i ∈ Ico a b, (Nat.primeCounting (n / Nat.nth Nat.Prime i) - i + 1) :=
  Nat.primeCounting_meissel hab hn hb hsq hcube hsquares

end PrimeFactorUnimodality.Tests
