import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCounting

/-! # Exact sieve-count interfaces and boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open PrimeFactorUnimodality
open Finset
open PrimeCert.Sieve

example {n bits : ℕ} (h : IsSieve n bits) :
    sievePrimeSet n bits = Nat.primesLE n := by
  exact PrimeFactorUnimodality.sievePrimeSet_eq h

example (n bits : ℕ) :
    (sievePrimeSet n bits).card =
      (if 2 ≤ n then 1 else 0) + (if 3 ≤ n then 1 else 0) +
        (wheelPrimeIndices n bits).card := by
  exact PrimeFactorUnimodality.sievePrimeSet_card n bits

example {N n bits : ℕ} (h : IsSieve N bits) (hn : n ≤ N) :
    IsSieve n bits := by
  exact PrimeFactorUnimodality.isSieve_restrict h hn

example {N n bits k : ℕ} (h : IsSieve N bits)
    (hn : n ≤ N) (hk : wheelLength n - 1 ≤ 2 ^ k) :
    Nat.primeCounting n = sievePrimeCount k n bits := by
  exact PrimeFactorUnimodality.primeCounting_eq_sievePrimeCount h hn hk

example {N k bits n count : ℕ} (h : IsSieve N bits)
    (hc : checkSievePrimeCount N k bits n count = true) : Nat.primeCounting n = count := by
  exact PrimeFactorUnimodality.primeCounting_eq_of_sieve_check h hc

example (k n bits : ℕ) : sievePrimeCount k n bits =
    (if 2 ≤ n then 1 else 0) + (if 3 ≤ n then 1 else 0) +
      Nat.bitCountBlock k bits 1 (wheelLength n - 1) := by
  simp only [sievePrimeCount, Nat.bitCountBlockPacked_eq]

private theorem sieve30 : IsSieve 30 766 :=
  isSieve_of_sieveK_eq (sqrtN := 6) (by decide +kernel) (by decide) (by decide)

example : Nat.primeCounting 30 = 10 :=
  primeCounting_eq_of_sieve_check sieve30 (k := 4) (by decide +kernel)
example : checkSievePrimeCount 30 0 766 4 2 = true := by decide +kernel
example : checkSievePrimeCount 30 4 766 28 9 = true := by decide +kernel
example : checkSievePrimeCount 30 4 767 28 9 = true := by decide +kernel
example : checkSievePrimeCount 30 3 766 30 10 = false := by decide +kernel
example : checkSievePrimeCount 30 4 766 31 11 = false := by decide +kernel
example : sievePrimeCount 0 0 1 = 0 ∧ sievePrimeCount 0 1 1 = 0 ∧
    sievePrimeCount 0 2 1 = 1 ∧ sievePrimeCount 0 3 1 = 2 := by decide +kernel

end PrimeFactorUnimodality.Tests
