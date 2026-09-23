import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCountIncrements

/-! # Exact sieve-count interfaces and boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open PrimeFactorUnimodality
open Finset
open PrimeCert.Sieve

example : Monotone wheelLength := by
  exact PrimeFactorUnimodality.wheelLength_mono

example {a : ℕ} (ha : 3 ≤ a) : 1 ≤ wheelLength a := by
  exact PrimeFactorUnimodality.one_le_wheelLength ha

example {N a bits : ℕ} (h : IsSieve N bits)
    (ha : 3 ≤ a) (haN : a ≤ N) :
    Nat.primeCounting a = 2 + (wheelPrimeIndices a bits).card := by
  exact PrimeFactorUnimodality.primeCounting_eq_two_add_wheelCard h ha haN

example {a b bits : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    (wheelPrimeIndices b bits).card = (wheelPrimeIndices a bits).card +
      ((range (wheelLength b - wheelLength a)).filter
        (fun i => bits.testBit (wheelLength a + i))).card := by
  exact PrimeFactorUnimodality.wheelPrimeIndices_card_add ha hab

example {N a b bits k : ℕ} (h : IsSieve N bits)
    (ha : 3 ≤ a) (hab : a ≤ b) (hbN : b ≤ N)
    (hk : wheelLength b - wheelLength a ≤ 2 ^ k) :
    Nat.primeCounting a + Nat.bitCountBlock k bits (wheelLength a)
      (wheelLength b - wheelLength a) = Nat.primeCounting b := by
  exact PrimeFactorUnimodality.primeCounting_add_bitCountBlock h ha hab hbN hk

example {N k bits a oldCount b newCount : ℕ}
    (h : IsSieve N bits) (ha : Nat.primeCounting a = oldCount)
    (hc : checkSieveCountStep N k bits a oldCount b newCount = true) :
    Nat.primeCounting b = newCount := by
  exact PrimeFactorUnimodality.primeCounting_eq_of_sieve_step h ha hc

private theorem sieve30 : IsSieve 30 766 :=
  isSieve_of_sieveK_eq (sqrtN := 6) (by decide +kernel) (by decide) (by decide)

example : checkSieveCountStep 30 2 766 3 2 11 5 = true := by decide +kernel
example : checkSieveCountStep 30 3 766 11 5 30 10 = true := by decide +kernel
example : checkSieveCountStep 30 0 766 11 5 11 5 = true := by decide +kernel
example : checkSieveCountStep 30 0 766 11 5 30 10 = false := by decide +kernel
example : checkSieveCountStep 30 4 766 11 5 3 2 = false := by decide +kernel
example : Nat.primeCounting 11 + Nat.bitCountBlock 3 766 (wheelLength 11)
    (wheelLength 30 - wheelLength 11) = Nat.primeCounting 30 :=
  primeCounting_add_bitCountBlock sieve30 (by decide) (by decide) (by decide) (by decide +kernel)

end PrimeFactorUnimodality.Tests
