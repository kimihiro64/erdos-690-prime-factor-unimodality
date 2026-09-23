import Mathlib.Tactic.IntervalCases
import PrimeFactorUnimodality.Helpers.Arithmetic.MeisselRows

/-! # MeisselRows: semantic and boundary regression tests -/

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

private def quotients (i : ℕ) : MeisselQuotientRow := match i with
  | 2 => ⟨8, 0⟩
  | 3 => ⟨6, 7⟩
  | _ => ⟨0, 11⟩

example : Nat.primeCounting 100 = 25 := by
  apply primeCounting_eq_of_meissel_rows (p := primes) (a := 2) (b := 4)
    (phi := 33) (rows := quotients)
  · intro i hi
    interval_cases i <;> simp [primes, Nat.nth_prime_zero_eq_two,
      Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
      Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  · exact phi100
  · intro i hi
    have := (mem_Ico.mp hi).1
    have := (mem_Ico.mp hi).2
    interval_cases i <;> decide +kernel
  · rfl
  · intro i hi
    have := (mem_Ico.mp hi).1
    have := (mem_Ico.mp hi).2
    interval_cases i <;> decide +kernel
  · decide +kernel

example : checkMeisselEndpoint primes 100 2 4 33 11 25 = true := by decide +kernel
example : checkMeisselEndpoint primes 3 1 1 2 0 2 = true := by decide +kernel

example : checkMeisselEndpoint primes 100 2 4 33 11 26 = false := by decide +kernel

example : checkMeisselEndpoint primes 121 2 4 33 11 25 = false := by decide +kernel

example : checkMeisselEndpoint primes 125 2 5 33 11 26 = false := by decide +kernel

example : checkMeisselEndpoint primes 100 4 2 33 11 23 = false := by decide +kernel

example : checkMeisselEndpoint primes 0 0 0 1 0 0 = false := by decide +kernel

example : checkMeisselEndpoint primes 40 1 4 33 11 25 = false := by decide +kernel

example : checkMeisselEndpoint primes 8 0 1 8 5 3 = false := by decide +kernel

example : checkMeisselQuotientRow (fun _ => ⟨8, 0⟩) 2 = false := by decide +kernel
example : checkMeisselQuotientRow quotients 2 = true := by decide +kernel
example : checkMeisselQuotientRow quotients 3 = true := by decide +kernel

end PrimeFactorUnimodality.Tests
