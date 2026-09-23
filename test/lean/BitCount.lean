import PrimeFactorUnimodality.Mathlib.Data.Nat.BitCount

/-! # Exact sieve-count interfaces and boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Nat
open Finset

example (k bits : ℕ) :
    bitCountPow k bits = ∑ i ∈ range (2 ^ k), if bits.testBit i then 1 else 0 := by
  exact Nat.bitCountPow_eq_sum k bits

example (k bits width : ℕ) (hw : width ≤ 2 ^ k) :
    bitCountPow k (bits % 2 ^ width) =
      ((range width).filter (fun i => bits.testBit i)).card := by
  exact Nat.bitCountPow_mod_eq_card k bits width hw

example (k bits start width : ℕ) (hw : width ≤ 2 ^ k) :
    bitCountBlock k bits start width =
      ((range width).filter (fun i => bits.testBit (start + i))).card := by
  exact Nat.bitCountBlock_eq_card k bits start width hw

example (k bits start a b : ℕ) (hab : a + b ≤ 2 ^ k) :
    bitCountBlock k bits start (a + b) =
      bitCountBlock k bits start a + bitCountBlock k bits (start + a) b := by
  exact Nat.bitCountBlock_append k bits start a b hab

example : bitCountBlock 1 13 2 2 = 2 := by decide +kernel
example : bitCountBlock 3 65535 3 0 = 0 := by decide +kernel
example : bitCountBlock 3 65535 3 5 = 5 := by decide +kernel
example : bitCountBlock 0 3 0 2 = 1 := by decide +kernel
example : bitCountBlock 4 43981 0 16 =
    bitCountBlock 4 43981 0 7 + bitCountBlock 4 43981 7 9 :=
  bitCountBlock_append 4 43981 0 7 9 (by decide)

end PrimeFactorUnimodality.Tests
