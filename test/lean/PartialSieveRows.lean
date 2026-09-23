import Mathlib.Tactic.IntervalCases
import PrimeFactorUnimodality.Helpers.Arithmetic.PartialSieveRows

/-! # PartialSieveRows: semantic and boundary regression tests -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Finset
open PrimeFactorUnimodality


private def primes (i : ℕ) : ℕ := match i with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | _ => 11

private def emptyKnown (_ : ℕ) : PartialSieveClaim := ⟨0, 0, 0⟩

private def phiRows (i : ℕ) : PartialSieveRow := match i with
  | 0 => ⟨⟨0, 100, 100⟩, .initial⟩
  | 1 => ⟨⟨0, 50, 50⟩, .initial⟩
  | 2 => ⟨⟨1, 100, 50⟩, .split 0 1⟩
  | 3 => ⟨⟨0, 33, 33⟩, .initial⟩
  | 4 => ⟨⟨0, 16, 16⟩, .initial⟩
  | 5 => ⟨⟨1, 33, 17⟩, .split 3 4⟩
  | _ => ⟨⟨2, 100, 33⟩, .split 2 5⟩

private theorem phiRows_valid : ∀ i < 7, (phiRows i).claim.Valid primes := by
  apply partialSieveRows_valid primes (known := emptyKnown) (knownSize := 0)
  · intro k hk; omega
  · intro i hi
    interval_cases i <;> decide +kernel

private theorem phi100 : (PartialSieveClaim.mk 2 100 33).Valid primes :=
  phiRows_valid 6 (by decide)

example : Nat.sievePhi primes 2 100 = 33 := phi100
example : Nat.coprimeCount 6 100 = 33 :=
  phi100.coprimeCount (by decide) (by decide)

private def changedRow (bad : PartialSieveRow) (i : ℕ) : PartialSieveRow :=
  if i = 6 then bad else phiRows i

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨2, 100, 34⟩, .split 2 5⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨2, 101, 33⟩, .split 2 5⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨3, 100, 33⟩, .split 2 5⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨2, 100, 33⟩, .split 6 5⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨2, 100, 33⟩, .split 7 5⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨2, 100, 33⟩, .split 5 2⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨2, 100, 33⟩, .known 0⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨2, 100, 100⟩, .initial⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes emptyKnown 0
    (changedRow (⟨⟨0, 100, 99⟩, .initial⟩)) 6 = false := by decide +kernel

example : checkPartialSieveRow primes (fun _ => ⟨0, 100, 100⟩) 1
    (fun _ => ⟨⟨0, 100, 100⟩, .known 0⟩) 0 = true := by decide +kernel
example : checkPartialSieveRow primes (fun _ => ⟨0, 100, 100⟩) 1
    (fun _ => ⟨⟨0, 100, 99⟩, .known 0⟩) 0 = false := by decide +kernel
example : checkPartialSieveRow primes (fun _ => ⟨0, 100, 100⟩) 1
    (fun _ => ⟨⟨0, 100, 100⟩, .known 1⟩) 0 = false := by decide +kernel
example {p : ℕ → ℕ} {known : ℕ → PartialSieveClaim} {size : ℕ}
    {rows : ℕ → PartialSieveRow} {a b : ℕ}
    (ha : ∀ i < a, checkPartialSieveRow p known size rows i = true)
    (hb : ∀ i, a ≤ i → i < b → checkPartialSieveRow p known size rows i = true) :
    ∀ i < b, checkPartialSieveRow p known size rows i = true :=
  checkPartialSieveRows_join ha hb

end PrimeFactorUnimodality.Tests
