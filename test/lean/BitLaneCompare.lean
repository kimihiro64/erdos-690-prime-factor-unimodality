import PrimeFactorUnimodality.Mathlib.Data.Nat.BitLaneCompare

/-! # Range guards, strictness and exhaustive small packed-comparison regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

example : Nat.checkBitLaneLt 0 0 0 0 = false := by decide +kernel
example : Nat.checkBitLaneLt 1 0 0 0 = true := by decide +kernel
example : Nat.checkBitLaneLt 1 0 1 0 = false := by decide +kernel
example : Nat.checkBitLaneLt 1 0 0 1 = false := by decide +kernel
example : Nat.checkBitLaneLt 8 1 254 255 = true := by decide +kernel
example : Nat.checkBitLaneLt 8 1 255 255 = false := by decide +kernel
example : Nat.checkBitLaneLt 8 1 255 254 = false := by decide +kernel
example : Nat.checkBitLaneLt 8 1 0 256 = false := by decide +kernel
example : Nat.checkBitLaneLt 8 1 65536 65537 = false := by decide +kernel
example : Nat.checkBitLaneLt 2 2 3 16 = false := by decide +kernel
example : Nat.checkBitLaneLt 2 3 (1 + 16 * 3) (2 + 16 * 3 + 256) = false := by decide +kernel
example : Nat.checkBitLaneLt 2 3 (1 + 16 * 2) (2 + 16 * 3 + 256) = true := by decide +kernel

example : ∀ x y : Fin 16, Nat.checkBitLaneLt 1 2 x.val y.val =
    decide (x.val &&& 5 = x.val ∧ y.val &&& 5 = y.val ∧
      x.val % 4 < y.val % 4 ∧ x.val / 4 < y.val / 4) := by decide +kernel

example (s n x y : ℕ) (h : Nat.checkBitLaneLt s n x y = true) (i : ℕ) (hi : i < n) :
    Nat.bitLaneDigit s x i < Nat.bitLaneDigit s y i :=
  Nat.bitLaneDigit_lt_of_check s n x y h i hi

end PrimeFactorUnimodality.Tests
